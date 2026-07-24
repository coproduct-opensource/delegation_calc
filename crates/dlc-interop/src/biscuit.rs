//! Real [Biscuit](https://www.biscuitsec.org) encoding of a DLC-D `says`-credential.
//!
//! The [native CBOR token](super::InteropToken) is the DLC-D wire form; this module carries that
//! credential inside a **genuine Biscuit token** — an append-only, Ed25519-signed-chained block
//! whose authority block holds the credential as a Datalog fact — so a Biscuit-native verifier
//! parses it and the embedded DLC credential still verifies with `dlc_crypto` (spec §1). The
//! `biscuit-auth` dependency is confined to this crate; `dlc-core` never sees it (the Aeneas fence).
//!
//! Mapping (spec/interop-says-biscuit.md §1): the DLC credential (issuer, audience, wire-term, sig),
//! serialized as the CBOR [`InteropToken`](super::InteropToken), is embedded as the fact
//! `dlc_says_credential("<hex>")` in the Biscuit's authority block, signed by the Biscuit root key.
//! Biscuit's own chain provides the append-only / offline-attenuation structure the Tamarin model
//! proves; the embedded DLC credential provides the machine-checked `says` typing + `verify_in_keyring`.

use biscuit_auth::{AuthorizerBuilder, Biscuit, KeyPair, PublicKey};

/// Errors from the Biscuit bridge.
#[derive(Debug, thiserror::Error)]
pub enum BiscuitError {
    /// The underlying `biscuit-auth` operation failed.
    #[error("biscuit error: {0}")]
    Biscuit(String),
    /// The Biscuit did not carry a `dlc_says_credential` fact (or it was malformed).
    #[error("no dlc_says_credential fact in the biscuit")]
    MissingCredential,
    /// The embedded credential hex was invalid.
    #[error("invalid credential encoding")]
    BadHex,
}

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn from_hex(s: &str) -> Result<Vec<u8>, BiscuitError> {
    if s.len() % 2 != 0 {
        return Err(BiscuitError::BadHex);
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| BiscuitError::BadHex))
        .collect()
}

/// Embed a DLC-D `says`-credential (its CBOR [`InteropToken`](super::InteropToken) bytes) into a
/// genuine Biscuit token signed by `root`, returning the real Biscuit wire bytes. The credential
/// rides as the authority fact `dlc_says_credential("<hex>")`.
///
/// # Errors
/// Propagates `biscuit-auth` build/serialize failures.
pub fn to_biscuit(credential_cbor: &[u8], root: &KeyPair) -> Result<Vec<u8>, BiscuitError> {
    let fact = format!("dlc_says_credential(\"{}\")", to_hex(credential_cbor));
    let biscuit = Biscuit::builder()
        .fact(fact.as_str())
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?
        .build(root)
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    biscuit
        .to_vec()
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))
}

/// Embed a DLC-D `says`-credential into a Biscuit that ALSO carries an EXPIRY, the wire realization
/// of DLC's revocable credential `within validUntil (p says φ)` (`spec/revocation-design.md`; the Lean
/// `acceptableAt`/`AcceptsRevocable` gate and the Tamarin `RevocationCheck` restriction). The authority
/// block gets a datalog check `check if dlc_now($t), $t <= validUntil`, so [`authorize_at`] rejects the
/// token once the clock passes `valid_until` (an integer epoch — seconds since the UNIX epoch).
///
/// # Errors
/// Propagates `biscuit-auth` build/serialize failures.
pub fn to_biscuit_with_expiry(
    credential_cbor: &[u8],
    valid_until: i64,
    root: &KeyPair,
) -> Result<Vec<u8>, BiscuitError> {
    let fact = format!("dlc_says_credential(\"{}\")", to_hex(credential_cbor));
    let check = format!("check if dlc_now($t), $t <= {valid_until}");
    let biscuit = Biscuit::builder()
        .fact(fact.as_str())
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?
        .check(check.as_str())
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?
        .build(root)
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    biscuit
        .to_vec()
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))
}

/// Authorize an (expiring) Biscuit at wall-clock epoch `now`: parse + verify against `root`, then run
/// the Biscuit authorizer with the fact `dlc_now(now)` and an `allow if true` policy. Returns `Ok(())`
/// iff every block check passes — in particular the expiry check `dlc_now($t), $t <= validUntil`, so an
/// EXPIRED token (`now > validUntil`) is rejected. This is DLC's `acceptableAt validUntil now` decided
/// on the real Biscuit wire.
///
/// # Errors
/// [`BiscuitError::Biscuit`] if the token does not parse/verify or authorization fails (expired, or no
/// matching allow policy).
pub fn authorize_at(biscuit_bytes: &[u8], root: PublicKey, now: i64) -> Result<(), BiscuitError> {
    let biscuit =
        Biscuit::from(biscuit_bytes, root).map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    let mut authorizer = AuthorizerBuilder::new()
        .code(format!("dlc_now({now});\nallow if true;"))
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?
        .build(&biscuit)
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    authorizer
        .authorize()
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    Ok(())
}

/// Parse + verify a Biscuit token (against the root public key) and extract the embedded DLC-D
/// `says`-credential's CBOR [`InteropToken`](super::InteropToken) bytes.
///
/// # Errors
/// [`BiscuitError::Biscuit`] if the token does not parse/verify; [`BiscuitError::MissingCredential`]
/// if it carries no `dlc_says_credential` fact.
pub fn from_biscuit(biscuit_bytes: &[u8], root: PublicKey) -> Result<Vec<u8>, BiscuitError> {
    let biscuit =
        Biscuit::from(biscuit_bytes, root).map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    let mut authorizer = biscuit
        .authorizer()
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    let rows: Vec<(String,)> = authorizer
        .query("data($d) <- dlc_says_credential($d)")
        .map_err(|e| BiscuitError::Biscuit(e.to_string()))?;
    let hex = &rows.first().ok_or(BiscuitError::MissingCredential)?.0;
    from_hex(hex)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{decode_credential, encode_credential, verify_credential};
    use dlc_core::judgment::KeyRing;
    use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
    use dlc_core::syntax::{Signature, Term};
    use dlc_protocol::wire;

    fn signed_credential_cbor() -> (KeyRing, Principal, Term, Signature, Vec<u8>) {
        let seed = [9u8; 32];
        let pk = dlc_crypto::ed25519::public_key(&seed);
        let issuer = Principal::Atom(PrincipalId(pk));
        let keyring = KeyRing {
            entries: vec![KeyRecord {
                principal: PrincipalId(pk),
                alg: 0,
                public_key: pk.to_vec(),
            }],
        };
        let term = Term::Var(0);
        let sig = Signature {
            alg: 0,
            bytes: dlc_crypto::ed25519::sign(&seed, &wire::canonical_bytes(&term)).to_vec(),
        };
        let cbor =
            encode_credential(&issuer, b"resource://tool/send_email", &term, &sig).expect("encode");
        (keyring, issuer, term, sig, cbor)
    }

    #[test]
    fn real_biscuit_round_trips_and_credential_still_verifies() {
        let (keyring, issuer, term, sig, cbor) = signed_credential_cbor();
        let root = KeyPair::new();

        // Embed into a REAL Biscuit; the output is genuine Biscuit wire bytes.
        let biscuit_bytes = to_biscuit(&cbor, &root).expect("to_biscuit");

        // A Biscuit-native verifier parses + verifies it (real Ed25519 block chain).
        let recovered = from_biscuit(&biscuit_bytes, root.public()).expect("from_biscuit");

        // The DLC credential is preserved byte-for-byte through the Biscuit.
        assert_eq!(recovered, cbor);

        // And the embedded says-credential still verifies with the DLC checker.
        let (issuer2, _aud, term2, sig2) = decode_credential(&recovered).expect("decode");
        assert_eq!(issuer2, issuer);
        assert_eq!(term2, term);
        assert_eq!(sig2, sig);
        assert!(verify_credential(&keyring, &issuer2, &term2, &sig2).is_ok());
    }

    #[test]
    fn expiring_biscuit_authorizes_before_and_fails_after() {
        let (keyring, issuer, term, sig, cbor) = signed_credential_cbor();
        let root = KeyPair::new();
        let valid_until = 1000i64;
        let bytes =
            to_biscuit_with_expiry(&cbor, valid_until, &root).expect("to_biscuit_with_expiry");

        // Before / at the bound: authorization succeeds.
        assert!(authorize_at(&bytes, root.public(), 500).is_ok());
        assert!(authorize_at(&bytes, root.public(), valid_until).is_ok());

        // After the bound: EXPIRED — authorization must fail (the wire realization of
        // `¬ acceptableAt validUntil now`).
        assert!(authorize_at(&bytes, root.public(), valid_until + 1).is_err());

        // The embedded DLC credential still round-trips and still verifies — expiry gates
        // acceptance without disturbing the carried says-credential.
        let recovered = from_biscuit(&bytes, root.public()).expect("from_biscuit");
        assert_eq!(recovered, cbor);
        let (issuer2, _aud, term2, sig2) = decode_credential(&recovered).expect("decode");
        assert_eq!(issuer2, issuer);
        assert_eq!(term2, term);
        assert_eq!(sig2, sig);
        assert!(verify_credential(&keyring, &issuer2, &term2, &sig2).is_ok());
    }

    #[test]
    fn wrong_root_key_rejects_the_biscuit() {
        let (_kr, _i, _t, _s, cbor) = signed_credential_cbor();
        let root = KeyPair::new();
        let biscuit_bytes = to_biscuit(&cbor, &root).expect("to_biscuit");
        // A different root key must not verify the token's signature chain.
        let attacker = KeyPair::new();
        assert!(from_biscuit(&biscuit_bytes, attacker.public()).is_err());
    }
}
