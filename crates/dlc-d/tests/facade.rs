//! End-to-end facade + lowering checks: users write `#[dlc_d::agent_service]` on a `fn`; the macro
//! lowers the parsed envelope — a `flow` axis becomes an `assert_flows_into` obligation, and a `cap`
//! axis appends a `Cap<Invoke<Tool>, Issuer>` witness parameter so callers must present the
//! capability. A well-formed envelope compiles; the violation classes live in `tests/ui/`.

use dlc_d::agent_service;
use dlc_d::labels::{Public, Secret};
use dlc_d::{Cap, Invoke};

// Capability types the `cap` axis names, and the grant that authorizes the demand below
// (the demanded-vs-granted gate rejects an ungranted pair at build — tests/ui/unauthorized_tool.rs).
#[derive(dlc_d::Tool)]
struct FileWrite;
struct Admin;

dlc_d::grants! { Admin: FileWrite }

// A fully-governed service: `Public ⊑ Secret` type-checks, and the macro appends a
// `Cap<Invoke<FileWrite>, Admin>` parameter — callers must present the capability witness.
#[agent_service(cap = Invoke<FileWrite> @ Admin, flow = Public <= Secret, budget = Faults<1>)]
fn governed_write() -> u32 {
    7
}

// Flow-only: no `cap` axis, so no witness parameter is appended.
#[agent_service(flow = Secret <= Secret)]
fn reflexive_flow() -> u32 {
    1
}

// A bare envelope lowers to nothing and keeps the original signature.
#[agent_service]
fn ungoverned() -> u32 {
    0
}

#[test]
fn governed_fns_run() {
    // `governed_write` requires the capability witness (Tier-1 admission).
    assert_eq!(
        governed_write(Cap::<Invoke<FileWrite>, Admin>::unchecked()),
        7
    );
    assert_eq!(reflexive_flow(), 1);
    assert_eq!(ungoverned(), 0);
}

#[test]
fn labels_are_reachable() {
    let _p = Public;
    let _s = Secret;
}
