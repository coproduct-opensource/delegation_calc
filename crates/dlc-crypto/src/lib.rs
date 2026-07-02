//! Cryptographic realization for DLC.
//!
//! Realizes the cryptographic-typing judgment `Γ ⊢_K M : φ` of T2. The logic
//! kernel (`dlc-core`) treats signatures as opaque byte strings; this crate
//! gives them meaning under a concrete signature scheme (Ed25519) and provides
//! the time-anchor and transparency-log substrates referenced by `◇_τ` and
//! revocation.

#![forbid(unsafe_code)]

pub mod ed25519;
pub mod signed_term;
pub mod time_anchor;
pub mod transparency;

/// Derive the stable principal id for a public key: SHA-256 of the raw
/// public-key bytes. (Phase-3 binds this to SPIFFE-ID hashes via
/// nucleus-identity; the hash-of-key form is the self-certifying default.)
pub fn principal_id(public_key: &[u8]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(public_key);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// Errors that arise during cryptographic realization.
#[derive(Debug, thiserror::Error)]
pub enum CryptoError {
    /// Signature did not verify under the named principal's key.
    #[error("signature verification failed")]
    SignatureInvalid,
    /// Algorithm identifier in a signature is not one we implement.
    #[error("unsupported signature algorithm: {0}")]
    UnsupportedAlgorithm(u8),
    /// The keyring did not contain a public key for the principal named.
    #[error("no key in keyring for principal")]
    PrincipalUnknown,
    /// Time-anchor proof did not validate.
    #[error("time anchor proof invalid")]
    AnchorInvalid,
    /// Transparency-log inclusion / non-inclusion proof did not validate.
    #[error("transparency proof invalid")]
    TransparencyInvalid,
}
