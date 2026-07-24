//! `trybuild` UI tests for the `#[dlc_d::agent_service]` lowering: the good program compiles, and
//! each violation class fails with a source-located diagnostic. `.stderr` is pinned to the pinned
//! toolchain (rust-version 1.89); regenerate with `TRYBUILD=overwrite`.

#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/good.rs");
    t.compile_fail("tests/ui/illegal_flow.rs");
    t.compile_fail("tests/ui/missing_cap.rs");
}
