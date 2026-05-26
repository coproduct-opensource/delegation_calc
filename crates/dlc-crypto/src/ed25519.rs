//! Ed25519 realization of the `says` signature.
//!
//! `says-I` requires that a term carry a signature over its canonical bytes
//! under the introducing principal's key. T2's cryptographic-typing judgment
//! defers signature checking to this module.

use crate::CryptoError;

/// Verify an Ed25519 signature over `message` using `public_key`.
pub fn verify(_public_key: &[u8], _message: &[u8], _signature: &[u8]) -> Result<(), CryptoError> {
    // Stub: production implementation routes through `ed25519-dalek`.
    Err(CryptoError::SignatureInvalid)
}
