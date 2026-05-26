//! Wire format for DLC proof terms.
//!
//! The schema (ABNF) is frozen in `spec/abnf.md`. Content-addressed: every
//! subterm hashes to a stable id, enabling selective recomputation and
//! cross-organizational caching.

/// Encode a proof term to its wire bytes (COSE_Sign1 envelope wrapping CBOR).
pub fn encode(_term: &dlc_core::syntax::Term) -> Vec<u8> {
    Vec::new()
}

/// Decode a wire byte string into a proof term.
pub fn decode(_bytes: &[u8]) -> Result<dlc_core::syntax::Term, crate::ProtocolError> {
    Err(crate::ProtocolError::Cbor("not implemented".into()))
}
