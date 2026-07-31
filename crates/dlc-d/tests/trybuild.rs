//! `trybuild` UI tests for the `#[dlc_d::agent_service]` fabric: the good program compiles, and each
//! of the three violation classes fails with a source-located diagnostic. `.stderr` is pinned to the
//! pinned toolchain (rust-version 1.89); regenerate with `TRYBUILD=overwrite`.

#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/good.rs");
    t.compile_fail("tests/ui/illegal_flow.rs"); // isolation           (E0277)
    t.compile_fail("tests/ui/missing_cap.rs"); // admission: witness  (E0061)
    t.compile_fail("tests/ui/unauthorized_tool.rs"); // admission: grant    (E0277, demanded-vs-granted)
    t.compile_fail("tests/ui/no_grants_decl.rs"); // onboarding: no grants! at all (friendly E0277)
    t.compile_fail("tests/ui/widening_delegation.rs"); // delegation: widening   (E0277 at the delegation site)
    t.compile_fail("tests/ui/delegate_without_cap.rs"); // delegate axis needs cap (macro error)
    t.compile_fail("tests/ui/over_budget.rs"); // budget              (const-eval)
}
