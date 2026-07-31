//! Violation: composing the ledger's declared envelope into a stricter one. The ledger tolerates
//! `Faults<1>`; a context demanding 2 exceeds it, and the budget comparison is a const-eval
//! assertion — evaluated eagerly in a `const` item, exactly as the macro emits it — so the breach
//! is a compile error, not a runtime surprise.
const _: () = dlc_d::assert_tolerates::<1, 2>();

fn main() {}
