//! Violation class: unauthorized invocation. The `cap` axis appends a capability-witness parameter,
//! so calling a governed service WITHOUT presenting the `Cap<Invoke<FileWrite>, Admin>` witness is a
//! `rustc` type error — the macro's Tier-1 admission control.
use dlc_d::agent_service;

#[derive(dlc_d::Tool)]
struct FileWrite;
struct Admin;

// The grant is declared, so the ONLY violation this fixture exhibits is the missing witness.
dlc_d::grants! { Admin: FileWrite }

#[agent_service(cap = Invoke<FileWrite> @ Admin)]
fn needs_cap() -> u32 {
    1
}

fn main() {
    // Missing the capability witness argument.
    let _ = needs_cap();
}
