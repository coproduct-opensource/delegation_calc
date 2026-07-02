//! Keyring-mediated verification of a `says-I` signature.
//!
//! The canonical byte encoding of terms lives in
//! `dlc-protocol::wire::canonical_bytes` (protocol depends on crypto, not
//! the reverse), so this module takes the already-encoded bytes. What it
//! adds over raw `ed25519::verify` is the keyring policy: principal
//! resolution, algorithm agreement, and the rule that only ATOMIC
//! principals sign (composite principals acquire authority through
//! `delegate`, never by holding a key).

use dlc_core::judgment::KeyRing;
use dlc_core::principal::{Principal, PrincipalId};
use dlc_core::syntax::Signature;

use crate::{ed25519, CryptoError};

/// Resolve `principal` in `keyring` and verify `sig` over `canonical`.
///
/// Fails with:
/// * `PrincipalUnknown` — non-atomic principal, or no keyring row for it;
/// * `UnsupportedAlgorithm` — the signature's `alg` is not implemented or
///   does not match the keyring row's `alg`;
/// * `SignatureInvalid` — the signature does not verify.
pub fn verify_in_keyring(
    keyring: &KeyRing,
    principal: &Principal,
    canonical: &[u8],
    sig: &Signature,
) -> Result<(), CryptoError> {
    let pid: &PrincipalId = match principal {
        Principal::Atom(pid) => pid,
        // Composite principals never hold keys directly.
        _ => return Err(CryptoError::PrincipalUnknown),
    };
    let record = keyring
        .entries
        .iter()
        .find(|r| &r.principal == pid)
        .ok_or(CryptoError::PrincipalUnknown)?;
    if sig.alg != ed25519::ALG_ED25519 || record.alg != ed25519::ALG_ED25519 {
        return Err(CryptoError::UnsupportedAlgorithm(sig.alg));
    }
    ed25519::verify(&record.public_key, canonical, &sig.bytes)
}
