//------------------------------------------------------------------------------
// SlangDoc.cpp
// Implementation of SlangDoc class
//
// SPDX-FileCopyrightText: Hudson River Trading
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "document/SlangDoc.h"

#include "Indexer.h"
#include "ServerDriver.h"
#include "document/ShallowAnalysis.h"
#include "document/SymbolTreeVisitor.h"
#include "lsp/URI.h"
#include "util/Logging.h"
#include "util/SlangExtensions.h"
#include <filesystem>
#include <fmt/format.h>
#include <fmt/ranges.h>
#include <stdexcept>
#include <string>
#include <string_view>

#include "slang/ast/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceLocation.h"
#include "slang/text/SourceManager.h"
namespace server {

using namespace slang;

SlangDoc::SlangDoc(ServerDriver& driver, URI uri, SourceBuffer buffer) :
    m_driver(driver), m_sourceManager(driver.sm), m_options(driver.options), m_uri(uri),
    m_buffer(buffer) {
}

std::shared_ptr<SlangDoc> SlangDoc::fromTree(ServerDriver& driver,
                                             std::shared_ptr<syntax::SyntaxTree> tree) {
    auto buffer = SourceBuffer{
        .data = driver.sm.getSourceText(tree->getSourceBufferIds()[0]),
        .id = tree->getSourceBufferIds()[0],
    };
    auto uri = URI::fromFile(driver.sm.getFullPath(tree->getSourceBufferIds()[0]));
    auto ret = std::make_shared<SlangDoc>(driver, uri, buffer);
    ret->m_tree = tree;
    ret->m_isFromBuildFile = true;
    return ret;
}

std::shared_ptr<SlangDoc> SlangDoc::fromText(ServerDriver& driver, const URI& uri,
                                             std::string_view text) {
    std::string_view path = uri.getPath();
    SourceBuffer buffer;

    // Check if this path was previously cached (e.g., from an include)
    // If so, we need to replace the old buffer with the editor's version
    if (driver.sm.isCached(path)) {
        auto existingBuffer = driver.sm.readSource(path, nullptr).value();
        SmallVector<char> newBuffer;
        newBuffer.insert(newBuffer.end(), text.begin(), text.end());
        if (newBuffer.empty() || newBuffer.back() != '\0')
            newBuffer.push_back('\0');
        buffer = driver.sm.replaceBuffer(existingBuffer.id, std::move(newBuffer));
    }
    else {
        buffer = driver.sm.assignText(path, text);
    }

    return std::make_shared<SlangDoc>(driver, uri, buffer);
}

std::shared_ptr<SlangDoc> SlangDoc::open(ServerDriver& driver, const URI& uri) {
    auto buffer = driver.sm.readSource(uri.getPath(), nullptr).value();
    return std::make_shared<SlangDoc>(driver, uri, buffer);
}

const std::string_view SlangDoc::getText() const {
    // null terminator is included in data
    return m_sourceManager.getSourceText(m_buffer.id);
}

std::shared_ptr<syntax::SyntaxTree> SlangDoc::getSyntaxTree() {
    if (!m_tree) {
        // Will read the cached file data if it exists
        if (!m_sourceManager.isLatestData(m_buffer.id)) {
            m_buffer = m_sourceManager.readSource(m_uri.getPath(), nullptr).value();
        }
        m_tree = syntax::SyntaxTree::fromBuffer(m_buffer, m_sourceManager, m_options);
    }
    else if (!hasValidBuffers(m_sourceManager, m_tree)) {
        // Tree has invalid buffers, need to reparse
        m_buffer = m_sourceManager.readSource(m_uri.getPath(), nullptr).value();
        m_tree = syntax::SyntaxTree::fromBuffer(m_buffer, m_sourceManager, m_options);
    }
    return m_tree;
}

slang::BufferID SlangDoc::getIncludeBuffer(const std::filesystem::path& includedPath) {
    auto tree = getSyntaxTree();
    if (tree.get() != m_includeBufferKey) {
        m_includeBuffers.clear();
        for (auto& meta : tree->getIncludeDirectives()) {
            if (meta.buffer.id.valid())
                m_includeBuffers.try_emplace(m_sourceManager.getFullPath(meta.buffer.id),
                                             meta.buffer.id);
        }
        m_includeBufferKey = tree.get();
    }
    auto it = m_includeBuffers.find(includedPath);
    return it != m_includeBuffers.end() ? it->second : slang::BufferID{};
}

std::shared_ptr<ShallowAnalysis> SlangDoc::getAnalysis(bool refreshDependencies) {
    if (!m_analysis || !m_analysis->hasValidBuffers() || refreshDependencies) {
        // Check if this file is an svh included by an owner package. Build-file docs are
        // top-level packages themselves and never members, so skip the (locked) index lookup.
        namespace fs = std::filesystem;
        std::optional<fs::path> ownerPath;
        if (!m_isFromBuildFile)
            ownerPath = m_driver.getIndexer().getOwningPackage(
                fs::path(std::string(m_uri.getPath())));
        if (ownerPath) {
            if (auto ownerDoc = m_driver.getDocument(URI::fromFile(*ownerPath))) {
                // Ask the owner for our buffer in its *current* tree. A reparse reassigns
                // include buffer ids, so we can't reuse the build-time id from the index; the
                // owner caches this lookup per tree version so members don't each rescan.
                auto myPath = fs::path(std::string(m_uri.getPath()));
                auto bufId = ownerDoc->getIncludeBuffer(myPath);
                if (bufId.valid()) {
                    m_ownerDoc = ownerDoc;
                    m_ownerBufferId = bufId;
                    auto ownerTree = ownerDoc->getSyntaxTree();
                    // Pull in the packages the owner imports so cross-package references inside
                    // this member (e.g. a type from another package the owner `import`s) resolve.
                    if (m_dependentDocuments.empty() || refreshDependencies)
                        m_dependentDocuments = m_driver.getDependentDocs(ownerTree);
                    std::vector<std::shared_ptr<syntax::SyntaxTree>> trees = {ownerTree};
                    for (const auto& dep : m_dependentDocuments) {
                        if (auto depTree = dep->getSyntaxTree())
                            trees.push_back(depTree);
                    }
                    m_analysis = std::make_shared<ShallowAnalysis>(
                        m_sourceManager, m_ownerBufferId, ownerTree, m_options, trees);
                    INFO("Analyzed member {} via owner {}", m_uri.getPath(),
                         ownerPath->string());
                    return m_analysis;
                }
            }
        }

        // Standalone analysis (not a member, or owner not found/changed)
        m_ownerDoc.reset();
        m_ownerBufferId = {};
        // Build-file docs normally skip getDependentDocs: a fully-expanded top-level (module/tb)
        // tree references the whole compiled universe, so the dependency walk would open
        // thousands of files. But a package/interface build-file has a bounded reference set and
        // needs the packages it `import`s resolved for cross-package navigation, so still walk it.
        bool computeDeps = !m_isFromBuildFile;
        if (m_isFromBuildFile) {
            for (auto& [decl, _] : getSyntaxTree()->getMetadata().nodeMeta) {
                if (decl->kind == syntax::SyntaxKind::PackageDeclaration ||
                    decl->kind == syntax::SyntaxKind::InterfaceDeclaration) {
                    computeDeps = true;
                    break;
                }
            }
        }
        if (computeDeps && (m_dependentDocuments.empty() || refreshDependencies)) {
            m_dependentDocuments = m_driver.getDependentDocs(getSyntaxTree());
        }
        std::vector<std::shared_ptr<syntax::SyntaxTree>> trees = {getSyntaxTree()};
        for (const auto& doc : m_dependentDocuments) {
            if (auto depTree = doc->getSyntaxTree()) {
                trees.push_back(depTree);
            }
        }
        m_analysis = std::make_shared<ShallowAnalysis>(m_sourceManager, m_buffer.id, m_tree,
                                                       m_options, trees);
        INFO("Analyzed {} with tops: {}", m_uri.getPath(),
             fmt::join(m_analysis->getCompilation()->getRoot().topInstances |
                           std::views::transform([](const auto& top) { return top->name; }),
                       ", "));
    }

    return m_analysis;
}

std::optional<slang::SourceLocation> SlangDoc::getLocation(const lsp::Position& position) {
    // Ensure owner is resolved so m_ownerBufferId is up to date
    getAnalysis();
    BufferID effectiveBuffer = m_ownerBufferId.valid() ? m_ownerBufferId : m_buffer.id;
    return m_sourceManager.getSourceLocation(effectiveBuffer, position.line, position.character);
}

std::string SlangDoc::getPrevText(const lsp::Position& position) {
    return std::string(
        m_sourceManager.getLine(m_buffer.id, position.line + 1).substr(0, position.character));
}

bool SlangDoc::textMatches(std::string_view text) {
    // Just compute line offsets to validate UTF-8
    auto bufText = getText();
    if (bufText.size() != text.size() + 1) {
        ERROR("Text size mismatch: have {}, expected {}", bufText.size(), text.size() + 1);
        return false;
    }
    if (std::memcmp(bufText.data(), text.data(), bufText.size()) != 0) {
        ERROR("Text content mismatch");
        return false;
    }
    return true;
}

void SlangDoc::onChange(const std::vector<lsp::TextDocumentContentChangeEvent>& contentChanges) {
    // From the LSP spec:
    //
    // The actual content changes. The content changes describe single state changes to the
    // document. So if there are two content changes c1 (at array index 0) and c2 (at array
    // index 1) for a document in state S then c1 moves the document from S to S' and c2 from
    // S' to S''. So c1 is computed on the state S and c2 is computed on the state S'.
    //
    // To mirror the content of a document using change events use the following approach:
    // - start with the same initial content
    // - apply the 'textDocument/didChange' notifications in the order you receive them.
    // - apply the `TextDocumentContentChangeEvent`s in a single notification in the order you
    //   receive them.
    //
    // Partial is defined in the variant first, so it will match first iff range and text are both
    // present. WholeDocument will match if text is present, but only be tried second. Less specific
    // cases are tried later.
    SmallVector<char> buffer;
    std::string_view textView = getText();
    std::vector<size_t> lineOffsets;

    if (contentChanges.size() == 0) {
        ERROR("Empty onChange event");
        return;
    }

    auto getOffsets = [&](lsp::Range range) {
        // Only one thread is able to call onchange, so the offsets remain valid without locking
        SourceManager::computeLineOffsets(textView, lineOffsets);
        auto& start = range.start;
        auto& end = range.end;
        auto startOffset = lineOffsets[start.line] + start.character;
        auto endOffset = lineOffsets[end.line] + end.character;
        if (start.line >= lineOffsets.size() || end.line >= lineOffsets.size()) {
            throw std::runtime_error(fmt::format("Range out of bounds: {},{} / {}", start.line,
                                                 end.line, lineOffsets.size()));
        }
        return std::make_pair(startOffset, endOffset);
    };

    auto ensureNullTerminated = [&]() {
        if (buffer.empty() || buffer.back() != '\0')
            buffer.push_back('\0');
    };

    // Single change (most common)
    rfl::visit(
        [&](const auto& change) {
            using T = std::decay_t<decltype(change)>;
            if constexpr (std::is_same_v<T, lsp::TextDocumentContentChangePartial>) {
                auto offsets = getOffsets(change.range);
                buffer.append(textView.begin(), textView.begin() + offsets.first);
                buffer.append(change.text.begin(), change.text.end());
                buffer.append(textView.begin() + offsets.second, textView.end());
            }
            else {
                buffer.append(change.text.begin(), change.text.end());
            }
        },
        contentChanges[0]);
    ensureNullTerminated();

    // More than one change is rare- typically things like rename actions, or if there's some lag.
    for (size_t i = 1; i < contentChanges.size(); i++) {
        textView = std::string_view{buffer.data(), buffer.size()};
        lineOffsets.clear();
        rfl::visit(
            [&](const auto& change) {
                using T = std::decay_t<decltype(change)>;
                if constexpr (std::is_same_v<T, lsp::TextDocumentContentChangePartial>) {
                    auto offsets = getOffsets(change.range);
                    // handle deletes
                    if (offsets.second > offsets.first) {
                        buffer.erase(buffer.begin() + offsets.first,
                                     buffer.begin() + offsets.second);
                    }
                    // handle inserts
                    buffer.insert(buffer.begin() + offsets.first, change.text.begin(),
                                  change.text.end());
                }
                else {
                    // WholeDocument collapses all prior changes
                    buffer.clear();
                    buffer.append(change.text.begin(), change.text.end());
                    ensureNullTerminated();
                }
            },
            contentChanges[i]);
    }
    m_buffer = m_sourceManager.replaceBuffer(m_buffer.id, std::move(buffer));

    // Invalidate pointers to old buffer
    m_tree.reset();
    m_analysis.reset();
}
bool SlangDoc::reloadBuffer() {
    auto result = m_sourceManager.reloadBuffer(m_buffer.id);
    if (!result) {
        ERROR("Failed to re-read buffer for {}: {}", m_uri.getPath(), result.error().message());
        return false;
    }
    m_buffer = *result;
    m_tree.reset();
    m_analysis.reset();
    return true;
}

void SlangDoc::issueParseDiagnostics(DiagnosticEngine& diagEngine) {
    for (auto& diag : getSyntaxTree()->diagnostics()) {
        diagEngine.issue(diag);
    }
}

void SlangDoc::issueDiagnosticsTo(DiagnosticEngine& diagEngine) {
    auto analysis = getAnalysis(true);
    auto& shallowComp = *analysis->getCompilation();

    // For member svhs, use the owner's tree for parse diags and the owner buffer for filtering.
    // For standalone docs, use own tree and own buffer (existing behavior).
    BufferID effectiveBuffer = m_ownerBufferId.valid() ? m_ownerBufferId : m_buffer.id;
    auto ownerDoc = m_ownerDoc.lock();
    auto parseTree = ownerDoc ? ownerDoc->getSyntaxTree() : getSyntaxTree();

    for (auto& diag : parseTree->diagnostics()) {
        if (m_sourceManager.getFullyOriginalLoc(diag.location).buffer() != effectiveBuffer)
            continue;
        diagEngine.issue(diag);
    }

    for (auto& diag : shallowComp.getSemanticDiagnostics()) {
        if (m_sourceManager.getFullyOriginalLoc(diag.location).buffer() != effectiveBuffer)
            continue;
        diagEngine.issue(diag);
    }

    for (auto& diag : analysis->getAnalysisDiags()) {
        if (m_sourceManager.getFullyOriginalLoc(diag.location).buffer() != effectiveBuffer)
            continue;
        diagEngine.issue(diag);
    }
}

std::vector<lsp::DocumentSymbol> SlangDoc::getSymbols() {
    // Resolve owner status first: m_ownerBufferId is only populated once getAnalysis() runs.
    auto analysis = getAnalysis();
    // For member svhs, build the outline from the svh's own tree so we only show
    // symbols defined in this file, not the entire owner package.
    if (m_ownerBufferId.valid()) {
        SymbolTreeVisitor visitor(m_sourceManager);
        return visitor.get_symbols(getSyntaxTree(), true);
    }
    return analysis->getDocSymbols();
}

std::vector<lsp::Range> SlangDoc::getInactiveRegions() {
    std::vector<lsp::Range> result;
    result.reserve(getAnalysis()->syntaxes.disabledRegions.size());

    for (const auto& region : getAnalysis()->syntaxes.disabledRegions) {
        result.push_back(toRange(region, m_sourceManager));
    }

    return result;
}

} // namespace server
