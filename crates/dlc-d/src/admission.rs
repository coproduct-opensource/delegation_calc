//! The host-facing admission API — a PEP-shaped surface over [`runtime::admit`](crate::runtime::admit).
//!
//! [`crate::runtime::admit`] returns `Result<(), AdmitError>`, which is the right shape for a `?`-using
//! caller but not for a *reference monitor* that composes many independent checks and reports a reason.
//! This module gives that caller a small, dependency-free [`Decision`] (`Admit` / `Deny(reason)`) and a
//! [`decide`] wrapper, so a host runtime maps DLC-D admission into its own verdict type in one line
//! (e.g. `nucleus`'s `portcullis_core::combinators::CheckResult`) without importing DLC-D's error enum
//! or knowing the credential layout.
//!
//! ## Where this plugs in
//!
//! `portcullis-core`'s admission checkpoint (`manifest::check_admission`) is **structural**: it validates
//! declared manifest fields (capabilities, sinks, instruction sources) and openly notes in its own
//! docstring that "a tool that lies in its manifest will pass admission." [`decide`] supplies the
//! conjunct that structural rules cannot: a *cryptographic, proof-carrying* admission — the invocation is
//! admitted iff the tool's issuer really signed a capability for THIS tool (real Ed25519), and that
//! positive verdict is backed by the machine-checked `admit_joint` theorem (no false admits on the
//! admission fragment; `lean/DLC/AdmitFrag.lean`). See `spec/nucleus-admission-integration.md` for the
//! full integration design and the `PolicyCheck` adapter.
//!
//! ## Trust boundary (what DLC-D proves vs. what the host supplies)
//!
//! DLC-D proves: a positive [`Decision::Admit`] means the presented signature genuinely verifies for the
//! tool's cap atom, and (via `admit_joint`) that the corresponding compile-time cap is a real `commit-I`
//! derivation. The **host** supplies: the [`KeyRing`](dlc_core::judgment::KeyRing) (which issuer keys are
//! trusted is a host provenance decision), the [`Principal`](dlc_core::principal::Principal) identity of
//! the issuer, and the binding of a runtime tool name to the compile-time `Cap<Invoke<Tool>, Issuer>`.
//! DLC-D does not decide *whose* keys to trust — only whether a given keyring admits a given credential.

use dlc_core::judgment::KeyRing;
use dlc_core::principal::Principal;
use dlc_core::syntax::Signature;

pub use crate::runtime::{admit, cap_atom, AdmitError};

/// A Policy-Enforcement-Point-shaped admission decision. Deliberately dependency-free and `'static` in
/// its reason so a host maps it into its own verdict type without allocation or lifetime plumbing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decision {
    /// The invocation is admitted: the issuer signed a valid capability for this tool.
    Admit,
    /// The invocation is refused, with a fixed human-readable reason. Fail-closed: any verification
    /// failure — bad signature, unknown issuer, or a credential minted for a different tool — lands here.
    Deny(&'static str),
}

impl Decision {
    /// Whether the invocation was admitted.
    #[must_use]
    pub fn is_admit(&self) -> bool {
        matches!(self, Decision::Admit)
    }
}

/// **Decide a tool invocation.** [`Decision::Admit`] iff `issuer` really signed a capability granting
/// `tool` (a real Ed25519 [`verify_in_keyring`](dlc_crypto::signed_term::verify_in_keyring) over the
/// tool's cap message); otherwise [`Decision::Deny`], fail-closed. This is the same check as
/// [`admit`], re-shaped into a monitor-friendly verdict.
#[must_use]
pub fn decide(keyring: &KeyRing, issuer: &Principal, tool: &str, sig: &Signature) -> Decision {
    match admit(keyring, issuer, tool, sig) {
        Ok(()) => Decision::Admit,
        Err(AdmitError::Unauthorized) => {
            Decision::Deny("unauthorized: no valid issuer-signed capability for this tool")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dlc_core::principal::{KeyRecord, PrincipalId};

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
        let mut msg = b"dlc-d/cap-invoke:".to_vec();
        msg.extend_from_slice(&cap_atom(tool).to_le_bytes());
        let sig = Signature {
            alg: 0,
            bytes: dlc_crypto::ed25519::sign(&seed, &msg).to_vec(),
        };
        (keyring, issuer, sig)
    }

    #[test]
    fn decide_admits_the_right_tool() {
        let (kr, issuer, sig) = signed_cap("SendEmail");
        assert_eq!(decide(&kr, &issuer, "SendEmail", &sig), Decision::Admit);
        assert!(decide(&kr, &issuer, "SendEmail", &sig).is_admit());
    }

    #[test]
    fn decide_denies_a_different_tool_fail_closed() {
        let (kr, issuer, sig) = signed_cap("SendEmail");
        // Same credential, wrong tool: the signature does not cover DeleteAll's atom → Deny.
        assert!(matches!(
            decide(&kr, &issuer, "DeleteAll", &sig),
            Decision::Deny(_)
        ));
    }

    #[test]
    fn decide_matches_admit() {
        // decide() is admit() re-shaped: they agree on every input.
        let (kr, issuer, sig) = signed_cap("SendEmail");
        for tool in ["SendEmail", "DeleteAll", ""] {
            assert_eq!(
                decide(&kr, &issuer, tool, &sig).is_admit(),
                admit(&kr, &issuer, tool, &sig).is_ok()
            );
        }
    }
}
