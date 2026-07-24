//! The well-formed governed service compiles: `Public ⊑ Secret` is a declared edge, and the caller
//! presents the required `Cap<Invoke<FileWrite>, Admin>` capability witness.
use dlc_d::agent_service;
use dlc_d::labels::{Public, Secret};
use dlc_d::{Cap, Invoke};

struct FileWrite;
struct Admin;

#[agent_service(cap = Invoke<FileWrite> @ Admin, flow = Public <= Secret, budget = Faults<1>)]
fn governed() -> u32 {
    1
}

fn main() {
    assert_eq!(governed(Cap::<Invoke<FileWrite>, Admin>::new()), 1);
}
