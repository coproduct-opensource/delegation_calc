//! Ed25519 realization of the `says` signature.
//!
//! `says-I` requires that a term carry a signature over its canonical bytes
//! under the introducing principal's key. The canonical bytes themselves are
//! produced by `dlc-protocol::wire::canonical_bytes` (the dependency arrow
//! points protocol → crypto, so this module deals only in raw byte slices).

use ed25519_dalek::{Signature as DalekSignature, Signer, SigningKey, Verifier, VerifyingKey};

use crate::CryptoError;

/// Algorithm identifier for Ed25519 in `Signature::alg` / `KeyRecord::alg`.
pub const ALG_ED25519: u8 = 0;

/// Verify an Ed25519 signature over `message` using `public_key`.
pub fn verify(public_key: &[u8], message: &[u8], signature: &[u8]) -> Result<(), CryptoError> {
    let pk_bytes: [u8; 32] = public_key
        .try_into()
        .map_err(|_| CryptoError::SignatureInvalid)?;
    let vk = VerifyingKey::from_bytes(&pk_bytes).map_err(|_| CryptoError::SignatureInvalid)?;
    let sig_bytes: [u8; 64] = signature
        .try_into()
        .map_err(|_| CryptoError::SignatureInvalid)?;
    let sig = DalekSignature::from_bytes(&sig_bytes);
    vk.verify(message, &sig)
        .map_err(|_| CryptoError::SignatureInvalid)
}

/// Sign `message` with the key derived from `seed` (32 bytes).
///
/// Ed25519 signing is deterministic given the key, which is what the
/// committed test vectors rely on.
pub fn sign(seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
    let sk = SigningKey::from_bytes(seed);
    sk.sign(message).to_bytes()
}

/// The public key for a 32-byte seed.
pub fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    SigningKey::from_bytes(seed).verifying_key().to_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_verify_round_trip() {
        let seed = [7u8; 32];
        let pk = public_key(&seed);
        let msg = b"canonical bytes of a term";
        let sig = sign(&seed, msg);
        assert!(verify(&pk, msg, &sig).is_ok());
    }

    #[test]
    fn tampered_message_rejected() {
        let seed = [7u8; 32];
        let pk = public_key(&seed);
        let sig = sign(&seed, b"original");
        assert!(verify(&pk, b"tampered", &sig).is_err());
    }

    #[test]
    fn wrong_key_rejected() {
        let seed = [7u8; 32];
        let other = [8u8; 32];
        let msg = b"message";
        let sig = sign(&seed, msg);
        assert!(verify(&public_key(&other), msg, &sig).is_err());
    }

    #[test]
    fn malformed_inputs_rejected() {
        assert!(verify(&[0u8; 31], b"m", &[0u8; 64]).is_err());
        assert!(verify(&[0u8; 32], b"m", &[0u8; 63]).is_err());
    }
}
