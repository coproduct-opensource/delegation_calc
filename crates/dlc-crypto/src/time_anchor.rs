//! Time anchors for the `◇_τ` modality.
//!
//! The calculus knows only an abstract `TimeBound`; this module realizes the
//! `now < τ` side condition against a concrete anchor source. Following the
//! plan's R-A4 mitigation, the anchor abstraction is parameterized — drand
//! and the NIST randomness beacon are alternate implementations of the same
//! trait, neither baked into the calculus.
//!
//! drand: League of Entropy, threshold-BLS signature over a counter, 30s
//! rounds. <https://drand.love>.
//!
//! NIST: NIST randomness beacon v2, ECDSA over SHA-512(prior + locally-seeded),
//! 60s pulses. <https://csrc.nist.gov/projects/interoperable-randomness-beacons>.
//!
//! Both produce a `(timestamp, commitment)` pair that the verifier checks
//! against the public key bundled into the proof.

use crate::CryptoError;

/// A verified time anchor: a wall-clock timestamp the verifier has proved
/// is honestly published by the anchor source. The proof is the threshold-
/// signature (drand) or ECDSA signature (NIST) over the round content.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AnchorTime {
    /// Milliseconds since UNIX epoch, as reported by the anchor.
    pub epoch_ms: u64,
    /// The anchor source that produced this time. Audit-only.
    pub source: AnchorSource,
}

/// The anchor sources DLC accepts at v1. Adding a new source requires (a) a
/// `verify_*` function in this module, (b) a key-pinning entry in the
/// verifier's keyring, (c) a spec/threat-model.md amendment, since each
/// source is its own trust anchor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnchorSource {
    /// drand mainnet, default group.
    Drand,
    /// NIST randomness beacon v2.
    NistBeacon,
    /// In-test deterministic anchor — never accepted in production builds.
    /// Gated by `#[cfg(test)]` callers; the verifier rejects it by default.
    Test,
}

/// Verify a drand round commitment. Returns the round's reported `epoch_ms`
/// on success.
///
/// Production implementation (M3.M16): parse `round`-indexed BLS group
/// signature, verify against the group public key pinned in the verifier
/// keyring. The genesis time + period maps the round to wall-clock.
///
/// Week-Q3 stub returns `AnchorInvalid` — the trait shape is what matters
/// for the calculus seam; correctness is M3.
pub fn verify_drand(
    _round: u64,
    _commitment: &[u8],
    _group_public_key: &[u8],
) -> Result<AnchorTime, CryptoError> {
    Err(CryptoError::AnchorInvalid)
}

/// Verify a NIST randomness-beacon pulse commitment.
pub fn verify_nist_beacon(
    _pulse_index: u64,
    _commitment: &[u8],
    _signing_certificate_der: &[u8],
) -> Result<AnchorTime, CryptoError> {
    Err(CryptoError::AnchorInvalid)
}

/// In-test deterministic anchor. **Never** accept in production paths.
#[cfg(test)]
pub fn verify_test_anchor(epoch_ms: u64) -> Result<AnchorTime, CryptoError> {
    Ok(AnchorTime {
        epoch_ms,
        source: AnchorSource::Test,
    })
}

/// Check that a time bound `τ` lies strictly after a verified anchor time.
/// This is what makes a `◇_τ φ` proof unforgeable across clock skew: the
/// verifier must believe `anchor.epoch_ms < τ`, not the local wall clock.
pub fn within_bound(anchor: AnchorTime, bound_epoch_ms: u64) -> bool {
    anchor.epoch_ms < bound_epoch_ms
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn within_bound_strict() {
        let anchor = verify_test_anchor(1_000_000).unwrap();
        assert!(within_bound(anchor, 1_000_001));
        assert!(!within_bound(anchor, 1_000_000));
        assert!(!within_bound(anchor, 999_999));
    }

    #[test]
    fn drand_stub_rejects() {
        // Drand verification is a stub until M3.M16; confirm the stub
        // signals failure rather than silently passing.
        assert!(verify_drand(123, &[0u8; 96], &[0u8; 48]).is_err());
    }

    #[test]
    fn nist_stub_rejects() {
        assert!(verify_nist_beacon(456, &[0u8; 64], &[0u8; 200]).is_err());
    }
}
