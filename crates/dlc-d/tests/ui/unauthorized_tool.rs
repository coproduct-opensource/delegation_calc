//! Violation class: unauthorized tool (demanded-vs-granted). The envelope demands
//! `Invoke<Delete> @ Admin`, but the crate's `grants!` table grants `Admin` only `FileWrite` — so
//! the build fails with a trait-bound error spanned at the demanded tool, before any code runs.
//! (Adding `Delete` to `Admin`'s grants turns this fixture green — see tests/ui/good.rs for the
//! granted twin.)
use dlc_d::agent_service;

struct FileWrite;
struct Delete;
struct Admin;

dlc_d::grants! { Admin: FileWrite }

#[agent_service(cap = Invoke<Delete> @ Admin)]
fn purge() -> u32 {
    1
}

fn main() {}
