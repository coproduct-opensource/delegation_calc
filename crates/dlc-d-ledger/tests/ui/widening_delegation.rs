//! Violation: a WIDENING delegation. The Treasury holds only `Credit`, so handing a delegate
//! `Seize` is refused at the delegation site — misdelegation can only narrow.
use dlc_d_ledger::{Seize, Treasury};

struct Rogue;

dlc_d::delegates! { Treasury => Rogue: Seize }

fn main() {}
