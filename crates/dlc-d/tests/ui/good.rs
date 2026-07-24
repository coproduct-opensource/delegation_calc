//! The well-formed governed service compiles: `Public ⊑ Secret` is a declared edge, the capability
//! types are defined, and the fault budget is a valid const.
use dlc_d::agent_service;
use dlc_d::labels::{Public, Secret};

struct FileWrite;
struct Admin;

#[agent_service(cap = Invoke<FileWrite> @ Admin, flow = Public <= Secret, budget = Faults<1>)]
fn governed() -> u32 {
    1
}

fn main() {
    assert_eq!(governed(), 1);
}
