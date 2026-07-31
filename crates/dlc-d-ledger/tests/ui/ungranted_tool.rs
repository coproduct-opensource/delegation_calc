//! Violation: the envelope demands a tool the issuer never granted. The Treasury grants only
//! `Credit` (`dlc_d::grants!` in the ledger crate); demanding `Seize` fails the demanded-vs-granted
//! gate at build time — and the same fact is re-decided by the verified checker in the emitted
//! certificate test.
use dlc_d::agent_service;
use dlc_d_ledger::{Seize, Treasury};

#[agent_service(cap = Invoke<Seize> @ Treasury)]
fn seize_funds() -> u32 {
    1
}

fn main() {}
