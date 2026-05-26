//! Transparency-log substrate for offline revocation.
//!
//! Revocation in DLC is an offline non-inclusion proof against a witnessed
//! transparency-log root, not an online lookup. The substrate reuses nucleus's
//! `nucleus-lineage` Merkle structure in Phase 3; this module is the seam.

use crate::CryptoError;

/// Verify that `content_hash` is *not* present in the transparency log whose
/// root is `witnessed_root`, using the supplied non-inclusion proof.
pub fn verify_non_inclusion(
    _content_hash: &[u8; 32],
    _witnessed_root: &[u8; 32],
    _proof: &[u8],
) -> Result<(), CryptoError> {
    Err(CryptoError::TransparencyInvalid)
}
