//! The *operational* (decidable) consensus surface — mirror of the executable
//! content of `DLCD.IsQuorum` / `DLCD.Decided` (`lean/DLCD/Consensus.lean`).
//!
//! The `Finset`/`Fin n` `Prop` forms (`agreement`, `quorum_intersect`,
//! `validity`, `committed_prefix_agree`) stay Lean-only — they are the
//! *guarantees* the Rust core must be shown to *serve*, not code to translate.
//! Here we mirror only the *decidable content*: the `2·card > n` quorum test
//! and a decidable `decided` witness.

use alloc::vec::Vec;

use dlc_core::rsm::Command;

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

/// The decidable **Byzantine** quorum test: a cardinality `card` exceeds two
/// thirds of `n`. Mirror of the *operationalized*
/// `DLCD.ByzantineConsensus.IsByzQuorum` (`3 * card > 2 * n`, i.e. `card ≥ 2f+1`
/// of `n = 3f+1`). Its safety rests on `byz_quorum_honest_intersect`: two such
/// quorums share `≥ f+1 > f` members, so at least one is honest.
///
/// This is the Aeneas-translated image the runtime Byzantine threshold
/// (`dlc_d_node::proto::Quorum::Byzantine`) is cross-checked against, so the
/// deployed threshold is the same predicate the Lean side reasons about — the
/// same relationship `is_quorum` has to the crash path. (The full agreement
/// *theorem* transport over an honest set stays backlog; see
/// `spec/r6-1b-replication-protocol.md` §6.5.)
pub fn is_byz_quorum(card: u32, n: u32) -> bool {
    3 * card > 2 * n
}

/// Decidable `decided`: some quorum unanimously voted for `v`. Operationalized
/// as "the number of replicas that voted *exactly* `v` is a quorum of the
/// electorate". The `∃ quorum. ∀ i ∈ quorum. votes i = v` `Prop` stays
/// Lean-only; this counts the witnessing index-set's cardinality directly.
///
/// Closure-free explicit loop (no `iter().filter().count()`).
///
/// Both allows are load-bearing, not laziness: clippy's suggested iterator form
/// and `if let` rewrite are the shapes the Aeneas fence forbids / the shape the
/// generated Lean image was drift-gated against, so taking the suggestions would
/// either produce opaque axioms or churn the translation. CI runs clippy with
/// `-D warnings`, so the allows have to be explicit.
#[allow(clippy::needless_range_loop, clippy::single_match)]
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

/// Decidable **Byzantine** `decided`: the number of replicas that voted exactly
/// `v` is a *Byzantine* quorum of the electorate. Identical to [`decided`] but
/// with the `3·card > 2n` threshold — the decision a leader on a Byzantine
/// roster must use so its commit clears the same bar its followers verify
/// against.
///
/// Closure-free explicit loop, same Aeneas fence as [`decided`].
#[allow(clippy::needless_range_loop, clippy::single_match)]
pub fn byz_decided(votes: &[Option<Command>], v: &Command) -> bool {
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
    is_byz_quorum(count, votes.len() as u32)
}
