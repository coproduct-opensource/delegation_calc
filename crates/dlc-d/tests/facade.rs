//! The facade path: users write `#[dlc_d::agent_service]` (re-exported from `dlc-d-macro`) and
//! reach the Tier-1 vocabulary as `dlc_d::{Cap, Invoke, FlowsInto, Faults}`. At this increment the
//! macro parses the envelope and passes the item through; enforcement (emitting the Tier-1 bounds
//! from the parsed axes) and the Tier-2 certificate land next.

use dlc_d::agent_service;
use dlc_d::labels::{Public, Secret};
use dlc_d::{assert_flows_into, Cap, Faults, Invoke};

#[agent_service(cap = Invoke<FileWrite> @ admin, flow = secret <= public, budget = Faults<1>)]
fn governed_write() -> u32 {
    7
}

#[test]
fn facade_governed_fn_runs() {
    assert_eq!(governed_write(), 7);
}

#[test]
fn facade_vocabulary_is_reachable() {
    let _cap: Cap<Invoke<FileWrite>, Admin> = Cap::new();
    let _budget: Faults<1> = Faults;
    assert_flows_into::<Public, Secret>();
}

struct FileWrite;
struct Admin;
