//! The verifier entry point.
//!
//! Takes a wire-format proof term, a claimed proposition, and a keyring.
//! Acceptance is EXACTLY the two conjuncts of the machine-checked T2
//! characterization (`lean/DLC/Correspondence.lean`,
//! `t2_propositional_correspondence`):
//!
//! 1. **logical typing** — `infer` (T1's algorithm) produces the claimed
//!    proposition, and
//! 2. **signature validity** — every `Sign` node embedded in the term
//!    verifies under the keyring against the canonical bytes of the
//!    signed subterm (`allSigsVerify` on the Lean side).
//!
//! The `assumptions` parameter is the verifier's trust anchors — the
//! additive context Γₐ the relying party already grants (e.g. a
//! `speaks-for` root it has configured). The bare [`verify`] uses the
//! empty context: the token must stand entirely on its own.

use dlc_core::judgment::{Ctx, KeyRing};
use dlc_core::syntax::{Prop, Term};

use crate::VerifyResult;

/// Verify a wire-format proof of `claimed` under `keyring`, with no
/// ambient assumptions.
pub fn verify(wire: &[u8], claimed: &Prop, keyring: &KeyRing) -> VerifyResult {
    verify_with_assumptions(wire, claimed, keyring, &[])
}

/// Verify a wire-format proof of `claimed` under `keyring`, granting the
/// hypotheses in `assumptions` as the additive context (in order:
/// de-Bruijn index 0 is `assumptions[0]`).
pub fn verify_with_assumptions(
    wire: &[u8],
    claimed: &Prop,
    keyring: &KeyRing,
    assumptions: &[Prop],
) -> VerifyResult {
    let term = match dlc_protocol::wire::decode(wire) {
        Ok(t) => t,
        Err(e) => {
            return VerifyResult::Fail {
                offset: 0,
                reason: format!("wire decode failed: {e}"),
            }
        }
    };

    // Conjunct 1: logical typing (T1's algorithm, propositional fragment).
    let ctx = Ctx {
        additive: assumptions.to_vec(),
        linear: Vec::new(),
    };
    match dlc_core::decide::infer(&ctx, &term) {
        Some(inferred) if &inferred == claimed => {}
        Some(inferred) => {
            return VerifyResult::Fail {
                offset: 0,
                reason: format!("logical typing mismatch: inferred {inferred:?}"),
            }
        }
        None => {
            return VerifyResult::Fail {
                offset: 0,
                reason: "logical typing failed: no derivation".into(),
            }
        }
    }

    // Conjunct 2: every embedded signature verifies (allSigsVerify).
    match all_sigs_verify(&term, keyring) {
        Ok(()) => VerifyResult::Ok,
        Err(reason) => VerifyResult::Fail { offset: 0, reason },
    }
}

/// Rust mirror of Lean's `Term.allSigsVerify`: every `Sign` node carries a
/// signature that verifies under the keyring against the canonical bytes
/// of the signed subterm. `Verify` nodes are elimination forms; the
/// introduction-side check on `Sign` is where validity is enforced
/// (matching the Lean definition exactly).
fn all_sigs_verify(term: &Term, keyring: &KeyRing) -> Result<(), String> {
    match term {
        Term::Sign(p, m, sig) => {
            let canonical = dlc_protocol::wire::canonical_bytes(m);
            dlc_crypto::signed_term::verify_in_keyring(keyring, p, &canonical, sig)
                .map_err(|e| format!("signature check failed at a Sign node: {e}"))?;
            all_sigs_verify(m, keyring)
        }
        Term::Var(_) | Term::Now(_) => Ok(()),
        Term::Lam(_, body) => all_sigs_verify(body, keyring),
        Term::App(f, x) => {
            all_sigs_verify(f, keyring)?;
            all_sigs_verify(x, keyring)
        }
        Term::Verify(_, m, _) => all_sigs_verify(m, keyring),
        Term::Delegate(m, n) | Term::Discharge(m, n) => {
            all_sigs_verify(m, keyring)?;
            all_sigs_verify(n, keyring)
        }
        Term::Attenuate(m, _) => all_sigs_verify(m, keyring),
        Term::LiftLabel(_, m) => all_sigs_verify(m, keyring),
        Term::Declassify(_, m, pi) => {
            all_sigs_verify(m, keyring)?;
            all_sigs_verify(pi, keyring)
        }
        Term::WithinIntro(_, m) => all_sigs_verify(m, keyring),
        Term::Pair(a, b) | Term::TensorIntro(a, b) | Term::LetTensor(a, b) => {
            all_sigs_verify(a, keyring)?;
            all_sigs_verify(b, keyring)
        }
        Term::Fst(a) | Term::Snd(a) | Term::Inl(_, a) | Term::Inr(_, a) | Term::SfExtract(a) => {
            all_sigs_verify(a, keyring)
        }
        Term::Case(s, l, r) => {
            all_sigs_verify(s, keyring)?;
            all_sigs_verify(l, keyring)?;
            all_sigs_verify(r, keyring)
        }
        Term::LetSays(_, s, b) => {
            all_sigs_verify(s, keyring)?;
            all_sigs_verify(b, keyring)
        }
    }
}
