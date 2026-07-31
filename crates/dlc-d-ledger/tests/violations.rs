//! **The demo's non-vacuity leg**: the five violation classes the governed ledger claims to
//! reject are compile errors, each with its diagnostic pinned.
//!
//! This is what makes "compilation is the proof" a checkable statement rather than a slogan —
//! the good program in `src/` compiles and runs, and each of these does not. `.stderr` files are
//! pinned to the repo toolchain; regenerate with `TRYBUILD=overwrite`.

#[test]
fn violations_do_not_compile() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/missing_witness.rs"); // admission: no witness at the call site
    t.compile_fail("tests/ui/ungranted_tool.rs"); // admission: issuer never granted the tool
    t.compile_fail("tests/ui/illegal_flow.rs"); // isolation: undeclared lattice edge
    t.compile_fail("tests/ui/over_budget.rs"); // failure envelope: budget breach
    t.compile_fail("tests/ui/widening_delegation.rs"); // delegation: widening
}
