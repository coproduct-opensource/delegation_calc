//! Runtime admission — the verify-then-authorize PEP that gives the compile-time [`Cap`](crate::Cap)
//! its VALIDITY.
//!
//! `#[dlc_d::agent_service]` proves the authority ENVELOPE is well-typed (admission is a `Cap<Invoke
//! <Tool>, Issuer>` argument the caller must supply; the Tier-2 certificate discharges the transported
//! `commit-I` typing — `admit_joint`, `lean/DLC/AdmitFrag.lean`). But the compile-time `Cap` is a
//! phantom the caller mints freely; its RUNTIME validity is a genuine, issuer-signed capability
//! credential. This module supplies that check: [`admit`] runs the real Ed25519
//! [`verify_in_keyring`](dlc_crypto::signed_term::verify_in_keyring) over a credential BOUND to the
//! tool, fail-closed.
//!
//! The two guarantees are **joined at the admission entry point, not collapsed**: the Lean side proves
//! *typeability* (the envelope is a real `commit-I` derivation), `dlc-crypto` proves *signature
//! validity*, and [`admit`] composes them — a tool invocation is admitted iff its cap is typed (macro,
//! compile time) AND the presented credential is genuinely signed for that tool (here, runtime).
//!
//! Pattern: verify-then-authorize / a Policy-Enforcement Point that binds a credential to an action
//! and fails closed — the 2026 agent-authorization idiom (Before-the-Tool-Call, arXiv 2603.20953;
//! Sovereign Execution Broker, arXiv 2606.20520).

use dlc_core::judgment::KeyRing;
use dlc_core::principal::Principal;
use dlc_core::syntax::Signature;

/// Why an admission was refused. Fail-closed: any failure means *not admitted*.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmitError {
    /// The credential is not a valid, issuer-signed grant for this tool: either the Ed25519 signature
    /// did not verify against the issuer's keyring entry, or it was signed for a DIFFERENT tool (the
    /// signature covers the tool's cap atom, so a wrong-tool credential fails to verify here).
    Unauthorized,
}

/// The capability atom for a tool: FNV-1a (32-bit) of the tool name — **byte-for-byte identical** to
/// what `#[dlc_d::agent_service]` computes at macro time (`dlc-d-macro/envelope.rs::atom_hash`). This
/// is the compile-time↔runtime BINDING: the type-level `Cap<Invoke<Tool>, Issuer>` the macro checks
/// and the runtime credential admitted here name the SAME atom.
pub fn cap_atom(tool: &str) -> u32 {
    let mut h: u32 = 0x811c_9dc5;
    for b in tool.bytes() {
        h ^= u32::from(b);
        h = h.wrapping_mul(0x0100_0193);
    }
    h
}

/// The message a capability credential signs: a domain-separated encoding of the tool's cap atom, so
/// the issuer's signature BINDS the grant to exactly one tool — a credential for tool A cannot admit
/// tool B (verifying A's signature against B's atom message fails).
fn cap_message(atom: u32) -> Vec<u8> {
    let mut m = b"dlc-d/cap-invoke:".to_vec();
    m.extend_from_slice(&atom.to_le_bytes());
    m
}

/// **★ Runtime admission — verify-then-authorize.** Admit an invocation of `tool` iff `issuer` really
/// signed a capability granting THAT tool: a real Ed25519 [`verify_in_keyring`] over the tool's cap
/// message. Fail-closed. This is the runtime validity the compile-time `Cap<Invoke<Tool>, Issuer>`
/// witness stands for.
///
/// # Errors
/// [`AdmitError::Unauthorized`] if the signature does not verify for this tool (bad signature, unknown
/// issuer, or a credential minted for a different tool).
pub fn admit(
    keyring: &KeyRing,
    issuer: &Principal,
    tool: &str,
    sig: &Signature,
) -> Result<(), AdmitError> {
    dlc_crypto::signed_term::verify_in_keyring(keyring, issuer, &cap_message(cap_atom(tool)), sig)
        .map_err(|_| AdmitError::Unauthorized)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dlc_core::principal::{KeyRecord, PrincipalId};

    /// An honest issuer signs a capability granting `tool`.
    fn signed_cap(tool: &str) -> (KeyRing, Principal, Signature) {
        let seed = [5u8; 32];
        let pk = dlc_crypto::ed25519::public_key(&seed);
        let issuer = Principal::Atom(PrincipalId(pk));
        let keyring = KeyRing {
            entries: vec![KeyRecord {
                principal: PrincipalId(pk),
                alg: 0,
                public_key: pk.to_vec(),
            }],
        };
        let sig_bytes = dlc_crypto::ed25519::sign(&seed, &cap_message(cap_atom(tool)));
        let sig = Signature {
            alg: 0,
            bytes: sig_bytes.to_vec(),
        };
        (keyring, issuer, sig)
    }

    #[test]
    fn valid_credential_for_the_right_tool_admits() {
        let (kr, issuer, sig) = signed_cap("SendEmail");
        assert_eq!(admit(&kr, &issuer, "SendEmail", &sig), Ok(()));
    }

    #[test]
    fn credential_for_a_different_tool_is_rejected() {
        // The credential was signed for SendEmail's cap atom; presenting it for DeleteAll must fail —
        // the signature does not cover DeleteAll's atom message. Tool-binding enforced by the signature.
        let (kr, issuer, sig) = signed_cap("SendEmail");
        assert_eq!(
            admit(&kr, &issuer, "DeleteAll", &sig),
            Err(AdmitError::Unauthorized)
        );
    }

    #[test]
    fn tampered_signature_is_rejected() {
        let (kr, issuer, mut sig) = signed_cap("SendEmail");
        sig.bytes[0] ^= 0xFF;
        assert_eq!(
            admit(&kr, &issuer, "SendEmail", &sig),
            Err(AdmitError::Unauthorized)
        );
    }

    #[test]
    fn unknown_issuer_is_rejected() {
        let (_kr, issuer, sig) = signed_cap("SendEmail");
        let empty = KeyRing { entries: vec![] };
        assert_eq!(
            admit(&empty, &issuer, "SendEmail", &sig),
            Err(AdmitError::Unauthorized)
        );
    }

    #[test]
    fn cap_atom_is_fnv1a_matching_the_macro() {
        // FNV-1a of the empty string is the offset basis — a spot-check that this is the same
        // algorithm `dlc-d-macro/envelope.rs::atom_hash` uses (else the compile-time Cap and the
        // runtime admit would name different atoms).
        assert_eq!(cap_atom(""), 0x811c_9dc5);
        // And it is deterministic + tool-sensitive.
        assert_ne!(cap_atom("SendEmail"), cap_atom("DeleteAll"));
    }
}
