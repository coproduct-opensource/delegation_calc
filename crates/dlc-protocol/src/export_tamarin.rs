//! Export a DLC term to a Tamarin-style trace fact dump.
//!
//! Phase-2 L2.5 deliverable (operational half): produce a text dump that
//! mirrors the events the Tamarin model in `models/tamarin/dlc.spthy`
//! would observe were the term executed at runtime. The companion Lean
//! `liftToDeriv` function (`lean/DLC/ProtocolCorrespondence.lean`) is
//! the formal correspondence — this exporter is the runtime side.
//!
//! Output format: one fact per line, in Tamarin-fact syntax.
//!   `Says(<principal>, <proposition>)`
//!   `SpeaksForIssued(<principal>, <principal>)`
//!   `DelegateAccept(<principal>, <principal>, <proposition>)`
//!   `Verify(<principal>, <proposition>)`
//!
//! The principal/proposition formats are deliberately abstract (hex of
//! their content-hash) so the output is parseable by external tooling.

use dlc_core::principal::Principal;
use dlc_core::syntax::{Prop, Term};

/// Render a `Term` as a sequence of Tamarin-fact lines.
///
/// Walks the term tree depth-first, emitting one line per DLC operation
/// the corresponds to a Tamarin event in `dlc.spthy`. The output is
/// deterministic for a given term, making it suitable as input to
/// downstream tooling (model fuzzers, audit log replayers).
pub fn term_to_tamarin(term: &Term) -> String {
    let mut out = String::new();
    walk_term(term, &mut out);
    out
}

fn principal_id(p: &Principal) -> String {
    match p {
        Principal::Atom(pid) => format!("'{}'", hex_short(&pid.0)),
        Principal::And(a, b) => format!("and({}, {})", principal_id(a), principal_id(b)),
        Principal::Or(a, b) => format!("or({}, {})", principal_id(a), principal_id(b)),
        Principal::Acting(a, b) => {
            format!("acting({}, {})", principal_id(a), principal_id(b))
        }
    }
}

fn hex_short(bytes: &[u8]) -> String {
    let mut s = String::new();
    for b in bytes.iter().take(8) {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn prop_id(p: &Prop) -> String {
    match p {
        Prop::Top => "top".to_string(),
        Prop::Bot => "bot".to_string(),
        Prop::Atom(n) => format!("atom({})", n),
        Prop::Imp(_, _) => "imp(...)".to_string(),
        Prop::And(_, _) => "and(...)".to_string(),
        Prop::Or(_, _) => "or(...)".to_string(),
        Prop::Says(pp, _) => format!("says({}, ...)", principal_id(pp)),
        Prop::SpeaksFor(pp, qq) => {
            format!("speaks_for({}, {})", principal_id(pp), principal_id(qq))
        }
        Prop::At(_, _) => "at(...)".to_string(),
        Prop::Boxed(_, _) => "boxed(...)".to_string(),
        Prop::Within(_, _) => "within(...)".to_string(),
        Prop::Tensor(_, _) => "tensor(...)".to_string(),
        Prop::Lolli(_, _) => "lolli(...)".to_string(),
        Prop::Replicated(_, _) => "replicated(...)".to_string(),
    }
}

fn walk_term(term: &Term, out: &mut String) {
    match term {
        Term::Sign(p, m, _sig) => {
            walk_term(m, out);
            out.push_str(&format!("Says({}, ?)\n", principal_id(p)));
        }
        Term::Verify(p, m, _sig) => {
            walk_term(m, out);
            out.push_str(&format!("Verify({}, ?)\n", principal_id(p)));
        }
        Term::Delegate(m, n) => {
            walk_term(m, out);
            walk_term(n, out);
            // Emit DelegateAccept with the principals we can extract
            // from m's outer Sign and n's outer Sign.
            if let (Term::Sign(p, _, _), Term::Sign(q, _, _)) = (m.as_ref(), n.as_ref()) {
                out.push_str(&format!(
                    "DelegateAccept({}, {}, ?)\n",
                    principal_id(p),
                    principal_id(q)
                ));
            }
        }
        Term::Attenuate(m, psi) => {
            walk_term(m, out);
            out.push_str(&format!("Attenuate({})\n", prop_id(psi)));
        }
        Term::Lam(_, body) => walk_term(body, out),
        Term::App(f, x) => {
            walk_term(f, out);
            walk_term(x, out);
        }
        // box_O(M, N) -- structural descent only. The obligation itself is
        // modelled by the hand-written Box_Issue / Discharge_Accept rules in
        // models/tamarin/dlc.spthy, not synthesised from a term, so this arm
        // emits no event and only walks the sub-terms.
        Term::Boxed(_, m, n) => {
            walk_term(m, out);
            walk_term(n, out);
        }
        Term::Discharge(m, n) => {
            walk_term(m, out);
            walk_term(n, out);
        }
        Term::LiftLabel(_, m) => walk_term(m, out),
        Term::Declassify(_, m, pi) => {
            walk_term(m, out);
            walk_term(pi, out);
        }
        Term::WithinIntro(_, m) => walk_term(m, out),
        Term::Pair(a, b) => {
            walk_term(a, out);
            walk_term(b, out);
        }
        Term::Fst(a) | Term::Snd(a) | Term::Inl(_, a) | Term::Inr(_, a) => walk_term(a, out),
        Term::Case(s, l, r) => {
            walk_term(s, out);
            walk_term(l, out);
            walk_term(r, out);
        }
        Term::TensorIntro(a, b) | Term::LetTensor(a, b) => {
            walk_term(a, out);
            walk_term(b, out);
        }
        // says-E binds x in the body; structural descent only.
        Term::SaysBind(_, s, b) => {
            walk_term(s, out);
            walk_term(b, out);
        }
        Term::LetSays(_, s, b) => {
            walk_term(s, out);
            walk_term(b, out);
        }
        Term::SfExtract(m) => {
            walk_term(m, out);
        }
        // command(M, c, ℓ) -- structural descent only; no Tamarin event this
        // increment (untyped/inert, DLC-D R1). The distributed commit protocol
        // is modelled separately in the DLCD Lean layer, not synthesised here.
        Term::Command(m, c, _l) => {
            walk_term(m, out);
            walk_term(c, out);
        }
        // runCmd(V, s) -- structural descent only (DLC-D R1-inc3).
        Term::RunCmd(v, s) => {
            walk_term(v, out);
            walk_term(s, out);
        }
        Term::Var(_) | Term::Now(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dlc_core::principal::PrincipalId;
    use dlc_core::syntax::Signature;

    fn p(n: u8) -> Principal {
        Principal::Atom(PrincipalId([n; 32]))
    }

    fn sig() -> Signature {
        Signature {
            alg: 0,
            bytes: vec![0xAB; 64],
        }
    }

    #[test]
    fn says_emits_one_line() {
        let t = Term::Sign(p(1), Box::new(Term::Var(0)), sig());
        let out = term_to_tamarin(&t);
        assert!(out.contains("Says("));
        assert_eq!(out.lines().count(), 1);
    }

    #[test]
    fn delegate_emits_three_lines() {
        let m = Term::Sign(p(1), Box::new(Term::Var(0)), sig());
        let n = Term::Sign(p(2), Box::new(Term::Var(1)), sig());
        let d = Term::Delegate(Box::new(m), Box::new(n));
        let out = term_to_tamarin(&d);
        // m -> Says line, n -> Says line, delegate -> DelegateAccept line
        assert_eq!(out.lines().count(), 3);
        assert!(out.contains("DelegateAccept("));
    }

    #[test]
    fn output_is_deterministic() {
        let t = Term::Sign(p(7), Box::new(Term::Var(0)), sig());
        assert_eq!(term_to_tamarin(&t), term_to_tamarin(&t));
    }
}
