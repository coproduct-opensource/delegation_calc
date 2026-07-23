//! The *operational* (decidable) consensus surface — mirror of the executable
//! content of `DLCD.IsQuorum` / `DLCD.Decided` (`lean/DLCD/Consensus.lean`).
//!
//! The `Finset`/`Fin n` `Prop` forms (`agreement`, `quorum_intersect`,
//! `validity`, `committed_prefix_agree`) stay Lean-only — they are the
//! *guarantees* the Rust core must be shown to *serve*, not code to translate.
//! Here we mirror only the *decidable content*: the `2·card > n` quorum test
//! and a decidable `decided` witness.

use alloc::vec::Vec;

use crate::state::Command;

/// A set of votes: `votes[i]` is replica `i`'s vote (`Some(cmd)` = voted for
/// that command, `None` = no vote). The decidable substrate over which the
/// `Prop`-level `Decided` quantifies.
pub type Votes = Vec<Option<Command>>;

/// The decidable quorum test: a cardinality `card` is a strict majority of `n`.
///
/// Mirror of the *operationalized* `DLCD.IsQuorum` (`2 * card > n`). The
/// `Finset`-cardinality form stays Lean-only.
pub fn is_quorum(card: u32, n: u32) -> bool {
    2 * card > n
}

/// Decidable `decided`: some quorum unanimously voted for `v`. Operationalized
/// as "the number of replicas that voted *exactly* `v` is a quorum of the
/// electorate". The `∃ quorum. ∀ i ∈ quorum. votes i = v` `Prop` stays
/// Lean-only; this counts the witnessing index-set's cardinality directly.
///
/// Closure-free explicit loop (no `iter().filter().count()`).
pub fn decided(votes: &[Option<Command>], v: &Command) -> bool {
    let mut count: u32 = 0;
    for i in 0..votes.len() {
        match &votes[i] {
            Some(c) => {
                if c == v {
                    count += 1;
                }
            }
            None => {}
        }
    }
    is_quorum(count, votes.len() as u32)
}
