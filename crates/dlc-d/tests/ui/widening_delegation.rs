//! Violation class: WIDENING delegation. `Admin` holds only `FileWrite`, and the delegation
//! tries to hand `Intern` a `Delete` capability the parent never had — refused at `cargo build`
//! by the demanded-vs-granted gate AT THE DELEGATION SITE. Misdelegation can only narrow.
//! (Narrowing the same declaration to `FileWrite` compiles — see tests/facade.rs.)
use dlc_d::delegates;

#[derive(dlc_d::Tool)]
struct FileWrite;
#[derive(dlc_d::Tool)]
struct Delete;
struct Admin;
struct Intern;

dlc_d::grants! { Admin: FileWrite }

delegates! { Admin => Intern: Delete }

fn main() {}
