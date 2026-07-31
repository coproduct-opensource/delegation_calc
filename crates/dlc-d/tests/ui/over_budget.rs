//! Violation class: fault-budget breach. A service tolerating 1 fault composed into a context that
//! requires 2 — `assert_tolerates::<1, 2>()` — is a compile error (const-eval failure), the macro
//! fabric's third rustc-checked guarantee alongside admission (missing_cap) and isolation (illegal_flow).
//!
//! Written as a `const` ITEM, not a call in `fn main()`: the item form is evaluated eagerly, and
//! the call form was observed to compile silently in another crate's trybuild context
//! (dlc-d-ledger), i.e. the pin would have stopped biting without anyone noticing. Same form the
//! macro emits.
const _: () = dlc_d::assert_tolerates::<1, 2>();

fn main() {}
