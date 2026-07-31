//! Violation: an illegal cross-agent flow. The ledger declares `Ledger ⊑ Audit` only; the reverse
//! edge does not exist, so a service claiming it fails the lattice trait bound.
use dlc_d::agent_service;
use dlc_d_ledger::{Audit, Ledger};

#[agent_service(flow = Audit <= Ledger)]
fn leak_audit_into_ledger() -> u32 {
    1
}

fn main() {}
