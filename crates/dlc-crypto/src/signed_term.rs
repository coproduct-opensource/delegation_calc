//! Canonical-bytes encoding of `Term` for signing.
//!
//! `says-I` signatures are over the deterministic byte encoding of the
//! underlying term. The encoding is content-addressed: SHA-256 of these bytes
//! is the term's transparency-log key.

use dlc_core::syntax::Term;

/// Produce the canonical byte encoding of `term` suitable for signing.
///
/// Stub returns an empty vector. M2.L2.3 fixes this with a round-trippable
/// CBOR-based canonical form that the Tamarin/ProVerif exporters also use.
pub fn canonical_bytes(_term: &Term) -> Vec<u8> {
    Vec::new()
}
