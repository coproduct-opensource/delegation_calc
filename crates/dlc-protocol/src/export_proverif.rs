//! Export a DLC term to a ProVerif-style trace fact dump.
//!
//! Phase-2 L2.5 deliverable (mirror of `export_tamarin`). Same data flow,
//! ProVerif applied-pi syntax for the events. One event per line in the
//! form `event_name(arg1, arg2, ...)`.

use dlc_core::principal::Principal;
use dlc_core::syntax::{Prop, Term};

pub fn term_to_proverif(term: &Term) -> String {
    let mut out = String::new();
    walk_term(term, &mut out);
    out
}

fn principal_id(p: &Principal) -> String {
    match p {
        Principal::Atom(pid) => format!("pk_{}", hex_short(&pid.0)),
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
        Prop::Atom(n) => format!("atom_{}", n),
        _ => "complex_prop".to_string(),
    }
}

fn walk_term(term: &Term, out: &mut String) {
    match term {
        Term::Sign(p, m, _sig) => {
            walk_term(m, out);
            out.push_str(&format!("Says({}, prop).\n", principal_id(p)));
        }
        Term::Verify(p, m, _sig) => {
            walk_term(m, out);
            out.push_str(&format!("Verify({}, prop).\n", principal_id(p)));
        }
        Term::Delegate(m, n) => {
            walk_term(m, out);
            walk_term(n, out);
            if let (Term::Sign(p, _, _), Term::Sign(q, _, _)) = (m.as_ref(), n.as_ref()) {
                out.push_str(&format!(
                    "DelegateAccept({}, {}, prop).\n",
                    principal_id(p),
                    principal_id(q)
                ));
            }
        }
        Term::Attenuate(m, psi) => {
            walk_term(m, out);
            out.push_str(&format!("Attenuate({}).\n", prop_id(psi)));
        }
        Term::Lam(_, body) => walk_term(body, out),
        Term::App(f, x) => {
            walk_term(f, out);
            walk_term(x, out);
        }
        // box_O(M, N) -- structural descent only; see the matching arm in
        // export_tamarin.rs. The obligation processes live in the
        // hand-written models/proverif/dlc.pv.
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
        Term::SfExtract(m) => walk_term(m, out),
        // command(M, c, ℓ) -- structural descent into payload and credential
        // subterm; no protocol fact this increment (untyped/inert, DLC-D R1).
        Term::Command(m, c, _l) => {
            walk_term(m, out);
            walk_term(c, out);
        }
        // runCmd(V, s) -- structural descent (DLC-D R1-inc3).
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
    fn says_emits_event_line() {
        let t = Term::Sign(p(1), Box::new(Term::Var(0)), sig());
        let out = term_to_proverif(&t);
        assert!(out.contains("Says("));
    }

    #[test]
    fn delegate_emits_full_chain() {
        let m = Term::Sign(p(1), Box::new(Term::Var(0)), sig());
        let n = Term::Sign(p(2), Box::new(Term::Var(1)), sig());
        let d = Term::Delegate(Box::new(m), Box::new(n));
        let out = term_to_proverif(&d);
        assert!(out.contains("DelegateAccept("));
        assert_eq!(out.lines().count(), 3);
    }
}
