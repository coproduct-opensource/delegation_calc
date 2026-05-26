//! Time anchors for the `◇_τ` modality.
//!
//! Parameterized over the anchor source (drand, NIST randomness beacon, custom
//! VDF). The calculus knows only `TimeBound`; this module is what verifies a
//! concrete anchor commitment.

use crate::CryptoError;

/// A trait-free anchor verification API. Trait objects are intentionally
/// avoided so the anchor selection is a compile-time choice; callers pick the
/// `verify_*` function appropriate to the anchor source.
pub fn verify_drand(_round: u64, _commitment: &[u8]) -> Result<u64, CryptoError> {
    Err(CryptoError::AnchorInvalid)
}

/// Verify a NIST randomness-beacon pulse commitment.
pub fn verify_nist_beacon(_pulse_index: u64, _commitment: &[u8]) -> Result<u64, CryptoError> {
    Err(CryptoError::AnchorInvalid)
}
