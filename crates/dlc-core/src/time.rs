//! Time as a modality.
//!
//! `◇_τ φ` requires a proof that `now < τ` from a trusted anchor. The anchor is
//! abstracted as a `TimeBound` here; Phase-3 realizations (drand, NIST beacon)
//! live in `dlc-crypto::time_anchor`.

/// A time-bound expression.
///
/// `epoch_ms` is wall-clock milliseconds since UNIX epoch. The verifier checks
/// inclusion against a trusted anchor commitment (drand round, beacon pulse)
/// at the realization layer, not here.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TimeBound {
    /// Deadline in milliseconds since UNIX epoch.
    pub epoch_ms: u64,
}
