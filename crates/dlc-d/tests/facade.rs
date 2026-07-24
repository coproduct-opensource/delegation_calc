//! End-to-end facade + lowering checks: users write `#[dlc_d::agent_service]` on a `fn`; the macro
//! lowers the parsed envelope onto sibling `const _` obligations referencing the Tier-1 vocabulary.
//! A well-formed envelope (legal flow `Public ⊑ Secret`) compiles; the violation classes live in
//! `tests/ui/` (trybuild compile-fail).

use dlc_d::agent_service;
use dlc_d::labels::{Public, Secret};

// Capability types the `cap` axis names (any type works; the axis anchors them).
struct FileWrite;
struct Admin;

// A fully-governed service: `Public ⊑ Secret` is a declared lattice edge, so the emitted
// `assert_flows_into::<Public, Secret>()` obligation type-checks.
#[agent_service(cap = Invoke<FileWrite> @ Admin, flow = Public <= Secret, budget = Faults<1>)]
fn governed_write() -> u32 {
    7
}

// Reflexive flow also type-checks.
#[agent_service(flow = Secret <= Secret)]
fn reflexive_flow() -> u32 {
    1
}

// A bare envelope lowers to nothing.
#[agent_service]
fn ungoverned() -> u32 {
    0
}

#[test]
fn governed_fns_run() {
    assert_eq!(governed_write(), 7);
    assert_eq!(reflexive_flow(), 1);
    assert_eq!(ungoverned(), 0);
}

#[test]
fn labels_are_reachable() {
    // The lowering references these; confirm they are the expected facade types.
    let _p = Public;
    let _s = Secret;
}
