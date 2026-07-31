//! Onboarding-path error quality: a `cap` envelope in a crate with NO `dlc_d::grants!`
//! declaration must fail `cargo build` with the actionable demanded-vs-granted diagnostic (the
//! `#[diagnostic::on_unimplemented]` note telling the user to declare the grant) — not a cryptic
//! unresolved-name error. This pins the FIRST error every new user of the macro will see.
use dlc_d::agent_service;

#[derive(dlc_d::Tool)]
struct FileWrite;
struct Admin;

// NOTE: no `dlc_d::grants!` anywhere in this crate.

#[agent_service(cap = Invoke<FileWrite> @ Admin)]
fn ungoverned() -> u32 {
    1
}

fn main() {}
