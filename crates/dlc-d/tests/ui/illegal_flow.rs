//! Violation class: illegal cross-agent flow. `Secret <= Public` asserts `Secret: FlowsInto<Public>`,
//! which is NOT a declared lattice edge (only `Public ⊑ Secret` is), so this must fail to compile
//! with a trait-bound error — the macro's Tier-1 isolation guarantee.
use dlc_d::agent_service;
use dlc_d::labels::{Public, Secret};

#[agent_service(flow = Secret <= Public)]
fn leaky() -> u32 {
    0
}

fn main() {}
