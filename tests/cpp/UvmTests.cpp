// SPDX-FileCopyrightText: Hudson River Trading
// SPDX-License-Identifier: MIT

#include "utils/ServerHarness.h"

// Tests for UVM-style package/`include svh routing.
// Fixture: tests/data/pkg_member/
//   pkg.sv      -- package with `define PKG_MACRO and `include "src/member.svh"
//   src/member.svh -- class using `PKG_MACRO
//   pkg_member.f   -- build file listing pkg.sv

TEST_CASE("MemberSvhAnalysisRoutedThroughPackage") {
    ServerHarness server("pkg_member");
    server.setBuildFile("pkg_member.f");

    // Opening member.svh standalone would produce an "unknown macro" error for `PKG_MACRO.
    // With owner routing, the analysis uses the package's fully-expanded tree, so the macro
    // is defined and no diagnostic is emitted.
    auto svh = server.openFile("src/member.svh");
    auto diags = svh.getDiagnostics();
    CHECK(diags.empty());
}

TEST_CASE("MemberSvhSymbolsFromOwnTree") {
    ServerHarness server("pkg_member");
    server.setBuildFile("pkg_member.f");

    // Document symbols for the svh should list MemberClass (defined in the svh),
    // not the package-level symbols from pkg.sv.
    auto svh = server.openFile("src/member.svh");
    auto symbols = svh.getSymbolTree();
    REQUIRE(symbols.size() == 1);
    CHECK(symbols[0].name == "MemberClass");
}

TEST_CASE("MemberResolvesSymbolFromPackageImportedByOwner") {
    // a_member.svh (member of pkg_a) references b_byte_t from pkg_b, which pkg_a `import`s.
    // Routing through pkg_a must also pull in pkg_b (an owner dependency) so the cross-package
    // type resolves — goto-def on b_byte_t should land in pkg_b.sv.
    ServerHarness server("pkg_cross");
    server.setBuildFile("pkg_cross.f");
    auto svh = server.openFile("src/a_member.svh");

    auto cursor = svh.after("b_by");
    auto defs = cursor.getDefinitions();
    REQUIRE(!defs.empty());
    CHECK(std::string(defs[0].targetUri.getPath()).find("pkg_b.sv") != std::string::npos);
}

TEST_CASE("BuildPackageResolvesImportedPackageSymbol") {
    // pkg_a.sv is itself a build source (listed in the .f), so it stays an isFromBuildFile doc on
    // open. Such docs normally skip dependency resolution, but a package build-file must still
    // resolve the packages it `import`s — goto-def on b_byte_t (a pkg_b type used at pkg_a scope)
    // should land in pkg_b.sv.
    ServerHarness server("pkg_cross");
    server.setBuildFile("pkg_cross.f");
    auto pa = server.openFile("pkg_a.sv");

    auto cursor = pa.after("b_by");
    auto defs = cursor.getDefinitions();
    REQUIRE(!defs.empty());
    CHECK(std::string(defs[0].targetUri.getPath()).find("pkg_b.sv") != std::string::npos);
}

TEST_CASE("GotoIncludeResolvesThroughIncludeOnceGuard") {
    ServerHarness server("nested_include");
    server.setBuildFile("nested_include.f");

    // wrapper.svh re-includes macros.svh, which top.sv already included with an include-once
    // guard. Slang leaves the repeat directive's IncludeMetadata.buffer invalid, but
    // go-to-definition on the include path should still resolve to macros.svh by reusing the
    // path that the first (valid) include resolved to.
    // Two-arg openFile: wrapper.svh has no top-level symbols (pure preprocessor), so the
    // single-arg overload's symbol assertion doesn't apply. Text matches disk so positions align.
    auto wrapper = server.openFile("wrapper.svh", "`include \"macros.svh\"\n");
    auto cursor = wrapper.after("`include \"");
    auto defs = cursor.getDefinitions();
    REQUIRE(!defs.empty());
    CHECK(std::string(defs[0].targetUri.getPath()).find("macros.svh") != std::string::npos);
}
