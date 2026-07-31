//! Violation: a governed write called WITHOUT its capability witness. The `cap` axis appends the
//! witness parameter, so the omission is an ordinary `rustc` arity error at the call site.
fn main() {
    let _ = dlc_d_ledger::credit(1);
}
