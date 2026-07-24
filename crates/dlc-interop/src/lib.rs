//! # `dlc-interop` — the says-credential ↔ Biscuit/RFC-8707 interop bridge.
//!
//! A DLC-D `says`-credential (`Term::Sign : Says(p, φ)`, realized by Ed25519 in `dlc-crypto`) is
//! the same object a Biscuit root block encodes: an issuer vouches, under its key, for a capability
//! bound to a resource AUDIENCE (RFC 8707 `resource`/`aud`, mirrored by commit-I's sink/label `ℓ`).
//! This crate encodes/decodes such a credential to/from a self-describing interop **token**,
//! **reusing `dlc_protocol::wire` verbatim** for the embedded proof term (the `codec.rs` discipline —
//! one deterministic encoder, no second canonical form to drift from), so the exact bytes the
//! signature covers are preserved across the bridge.
//!
//! The protocol this realizes is machine-verified under Dolev–Yao: `models/tamarin/dlcd-interop.spthy`
//! (5 lemmas + differential bite) and `models/proverif/dlcd-interop.pv` (cross-check). The key
//! guarantee the *bridge* must preserve is that a credential the verifier accepts stays acceptable
//! after a round trip — pinned by [`tests`].
//!
//! ## Fences
//! - **First increment: a native CBOR interop token.** The actual `biscuit-auth` wire bytes (a real
//!   Biscuit) are a follow-up; that dep will be confined to this crate (never `dlc-core`, whose
//!   Aeneas fence bans third-party deps).
//! - **Partial-correctness**, like the rest of the transport: this joins a *typed* credential to a
//!   *signed* token; it does not collapse the two guarantees.

#![forbid(unsafe_code)]

use dlc_core::principal::{Principal, PrincipalId};
use dlc_core::syntax::{Signature, Term};
use dlc_protocol::wire;

/// Errors from the interop bridge.
#[derive(Debug, thiserror::Error)]
pub enum InteropError {
    /// The token bytes were not valid CBOR in the expected shape.
    #[error("interop token decode failed: {0}")]
    Decode(String),
    /// The embedded proof term did not decode via `dlc_protocol::wire`.
    #[error("embedded term decode failed: {0}")]
    Term(String),
    /// The issuer is not an atomic principal (only `Principal::Atom` is a keyring subject).
    #[error("issuer is not an atomic principal")]
    NonAtomicIssuer,
}

/// The self-describing interop token: an issuer-signed, audience-bound `says`-credential. The
/// `term` field is the embedded proof term in `dlc_protocol::wire` bytes — exactly the bytes the
/// signature covers (`wire::canonical_bytes`), so verification survives the round trip.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct InteropToken {
    /// The issuer's principal id (32 bytes) — the Biscuit root key's principal.
    pub issuer: [u8; 32],
    /// The resource audience (RFC 8707 `aud`/`resource`; DLC-D's sink/label `ℓ`).
    pub audience: Vec<u8>,
    /// The embedded proof term, in `dlc_protocol::wire` bytes (the signed payload).
    pub term: Vec<u8>,
    /// Signature algorithm identifier (Ed25519 = 0).
    pub sig_alg: u8,
    /// The credential signature bytes.
    pub sig: Vec<u8>,
}

/// Encode a `says`-credential — `issuer`, the resource `audience`, the signed proof `term`, and its
/// `sig` — into interop token bytes. The term is serialized with `dlc_protocol::wire::encode`, so
/// the signed bytes are preserved.
///
/// # Errors
/// Returns [`InteropError::NonAtomicIssuer`] if `issuer` is not a `Principal::Atom`.
pub fn encode_credential(
    issuer: &Principal,
    audience: &[u8],
    term: &Term,
    sig: &Signature,
) -> Result<Vec<u8>, InteropError> {
    let Principal::Atom(PrincipalId(id)) = issuer else {
        return Err(InteropError::NonAtomicIssuer);
    };
    let token = InteropToken {
        issuer: *id,
        audience: audience.to_vec(),
        term: wire::encode(term),
        sig_alg: sig.alg,
        sig: sig.bytes.clone(),
    };
    let mut buf = Vec::new();
    ciborium::into_writer(&token, &mut buf).expect("encoding to Vec cannot fail");
    Ok(buf)
}

/// Decode interop token bytes back into `(issuer, audience, term, sig)`.
///
/// # Errors
/// [`InteropError::Decode`] if the bytes are not a valid token; [`InteropError::Term`] if the
/// embedded term does not decode.
pub fn decode_credential(
    bytes: &[u8],
) -> Result<(Principal, Vec<u8>, Term, Signature), InteropError> {
    let token: InteropToken =
        ciborium::from_reader(bytes).map_err(|e| InteropError::Decode(e.to_string()))?;
    let term = wire::decode(&token.term).map_err(|e| InteropError::Term(format!("{e:?}")))?;
    let issuer = Principal::Atom(PrincipalId(token.issuer));
    let sig = Signature {
        alg: token.sig_alg,
        bytes: token.sig,
    };
    Ok((issuer, token.audience, term, sig))
}

/// Verify a decoded credential against a keyring: the issuer's signature must cover exactly the
/// term's canonical bytes. Thin wrapper over `dlc_crypto::signed_term::verify_in_keyring` — the
/// verified forgery-resistance the Tamarin/ProVerif models establish.
///
/// # Errors
/// Propagates `dlc_crypto`'s `CryptoError` (unknown principal, algorithm mismatch, bad signature).
pub fn verify_credential(
    keyring: &dlc_core::judgment::KeyRing,
    issuer: &Principal,
    term: &Term,
    sig: &Signature,
) -> Result<(), dlc_crypto::CryptoError> {
    dlc_crypto::signed_term::verify_in_keyring(keyring, issuer, &wire::canonical_bytes(term), sig)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dlc_core::judgment::KeyRing;
    use dlc_core::principal::KeyRecord;

    // Build an honest issuer + a genuinely signed credential.
    fn signed_credential() -> (KeyRing, Principal, Term, Signature) {
        let seed = [7u8; 32];
        let pk = dlc_crypto::ed25519::public_key(&seed);
        // principal id = its public key (self-authenticating).
        let issuer = Principal::Atom(PrincipalId(pk));
        let keyring = KeyRing {
            entries: vec![KeyRecord {
                principal: PrincipalId(pk),
                alg: 0,
                public_key: pk.to_vec(),
            }],
        };
        // The signed payload term (any term; the bridge preserves it + its signature).
        let term = Term::Var(0);
        let canonical = wire::canonical_bytes(&term);
        let sig_bytes = dlc_crypto::ed25519::sign(&seed, &canonical);
        let sig = Signature {
            alg: 0,
            bytes: sig_bytes.to_vec(),
        };
        (keyring, issuer, term, sig)
    }

    #[test]
    fn round_trip_preserves_verification() {
        let (keyring, issuer, term, sig) = signed_credential();
        let audience = b"resource://tool/send_email".to_vec();

        // Baseline: the credential verifies before the bridge.
        assert!(verify_credential(&keyring, &issuer, &term, &sig).is_ok());

        // Encode → decode.
        let bytes = encode_credential(&issuer, &audience, &term, &sig).expect("encode");
        let (issuer2, audience2, term2, sig2) = decode_credential(&bytes).expect("decode");

        // The credential is preserved exactly.
        assert_eq!(issuer2, issuer);
        assert_eq!(audience2, audience);
        assert_eq!(term2, term);
        assert_eq!(sig2, sig);

        // And it STILL verifies after the round trip — the bridge preserved the signed bytes.
        assert!(verify_credential(&keyring, &issuer2, &term2, &sig2).is_ok());
    }

    #[test]
    fn tampered_signature_fails_verification() {
        let (keyring, issuer, term, mut sig) = signed_credential();
        sig.bytes[0] ^= 0xFF; // flip a signature bit
        let audience = b"resource://tool/send_email".to_vec();
        let bytes = encode_credential(&issuer, &audience, &term, &sig).expect("encode");
        let (issuer2, _aud, term2, sig2) = decode_credential(&bytes).expect("decode");
        // A tampered credential must be rejected — the checker is the trust anchor.
        assert!(verify_credential(&keyring, &issuer2, &term2, &sig2).is_err());
    }

    #[test]
    fn corrupt_token_bytes_fail_to_decode() {
        assert!(decode_credential(b"\xff\xff not a token").is_err());
    }
}
