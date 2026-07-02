//! COSE_Sign1 envelope for DLC tokens (RFC 9052).
//!
//! The envelope frames a wire-encoded token for transport: payload =
//! `wire::encode(term)`, protected header carries `alg: EdDSA` and
//! `kid` = the PRESENTER's principal id, and the COSE signature is the
//! presenter's Ed25519 signature over the RFC 9052 `Sig_structure`.
//!
//! Semantics, stated precisely so nobody over-reads this:
//! * The AUTHORITY claims of a token live in its interior `Sign` nodes
//!   (`says-I`), checked by `dlc-verifier` against the canonical bytes
//!   of each signed subterm. The envelope adds none.
//! * The envelope binds the OUTERMOST bytes to a presenter key —
//!   transport integrity and proof-of-possession framing. It is NOT
//!   part of the attacker-based T2 obligation (open; see the ledger),
//!   and unwrapping it does not weaken or strengthen what the verifier
//!   checks inside.

use coset::{iana, CborSerializable, CoseSign1, CoseSign1Builder, HeaderBuilder};
use dlc_core::judgment::KeyRing;
use dlc_core::principal::PrincipalId;
use dlc_crypto::ed25519;

use crate::ProtocolError;

/// Wrap `token` (wire-encoded term bytes) in a COSE_Sign1 envelope,
/// signed by the presenter whose signing seed is `seed`. The `kid`
/// header is set to the presenter's principal id (SHA-256 of the
/// public key), which [`unwrap_sign1`] resolves through the keyring.
pub fn wrap_sign1(token: &[u8], seed: &[u8; 32]) -> Result<Vec<u8>, ProtocolError> {
    let pk = ed25519::public_key(seed);
    let kid = dlc_crypto::principal_id(&pk);
    let protected = HeaderBuilder::new()
        .algorithm(iana::Algorithm::EdDSA)
        .key_id(kid.to_vec())
        .build();
    let sign1 = CoseSign1Builder::new()
        .protected(protected)
        .payload(token.to_vec())
        .create_signature(b"", |pt| ed25519::sign(seed, pt).to_vec())
        .build();
    sign1
        .to_vec()
        .map_err(|e| ProtocolError::Cose(format!("{e}")))
}

/// Unwrap a COSE_Sign1 envelope: resolve the `kid` header in `keyring`,
/// verify the presenter signature, and return the inner token bytes
/// plus the presenter's principal id. The caller still runs the DLC
/// verifier on the returned bytes — this only checks the envelope.
pub fn unwrap_sign1(
    cose: &[u8],
    keyring: &KeyRing,
) -> Result<(Vec<u8>, PrincipalId), ProtocolError> {
    let sign1 =
        CoseSign1::from_slice(cose).map_err(|e| ProtocolError::Cose(format!("{e}")))?;
    let kid: [u8; 32] = sign1
        .protected
        .header
        .key_id
        .as_slice()
        .try_into()
        .map_err(|_| ProtocolError::Cose("kid: expected 32 bytes".into()))?;
    let pid = PrincipalId(kid);
    let record = keyring
        .entries
        .iter()
        .find(|r| r.principal == pid)
        .ok_or_else(|| ProtocolError::Cose("presenter not in keyring".into()))?;
    if record.alg != ed25519::ALG_ED25519 {
        return Err(ProtocolError::Cose("unsupported presenter alg".into()));
    }
    sign1
        .verify_signature(b"", |sig, data| {
            ed25519::verify(&record.public_key, data, sig).map_err(|_| ())
        })
        .map_err(|_| ProtocolError::Cose("presenter signature invalid".into()))?;
    let payload = sign1
        .payload
        .ok_or_else(|| ProtocolError::Cose("missing payload".into()))?;
    Ok((payload, pid))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dlc_core::principal::KeyRecord;

    fn keyring_for(seed: &[u8; 32]) -> (KeyRing, PrincipalId) {
        let pk = ed25519::public_key(seed);
        let pid = PrincipalId(dlc_crypto::principal_id(&pk));
        (
            KeyRing {
                entries: vec![KeyRecord {
                    principal: pid.clone(),
                    alg: ed25519::ALG_ED25519,
                    public_key: pk.to_vec(),
                }],
            },
            pid,
        )
    }

    #[test]
    fn wrap_unwrap_round_trip() {
        let seed = [0x11u8; 32];
        let (keyring, pid) = keyring_for(&seed);
        let token = b"not-really-a-token-but-any-bytes".to_vec();
        let cose = wrap_sign1(&token, &seed).unwrap();
        let (payload, presenter) = unwrap_sign1(&cose, &keyring).unwrap();
        assert_eq!(payload, token);
        assert_eq!(presenter, pid);
    }

    #[test]
    fn corrupt_envelope_rejected() {
        let seed = [0x11u8; 32];
        let (keyring, _) = keyring_for(&seed);
        let mut cose = wrap_sign1(b"payload", &seed).unwrap();
        let n = cose.len();
        cose[n - 1] ^= 0x01;
        assert!(unwrap_sign1(&cose, &keyring).is_err());
    }

    #[test]
    fn unknown_presenter_rejected() {
        let seed = [0x11u8; 32];
        let other = [0x22u8; 32];
        let (keyring, _) = keyring_for(&other);
        let cose = wrap_sign1(b"payload", &seed).unwrap();
        assert!(unwrap_sign1(&cose, &keyring).is_err());
    }
}
