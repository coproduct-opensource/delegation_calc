//! Violation class: fault-budget breach. A service tolerating 1 fault composed into a context that
//! requires 2 — `assert_tolerates::<1, 2>()` — is a compile error (const-eval failure), the macro
//! fabric's third rustc-checked guarantee alongside admission (missing_cap) and isolation (illegal_flow).
fn main() {
    dlc_d::assert_tolerates::<1, 2>();
}
