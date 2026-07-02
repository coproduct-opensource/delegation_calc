//! End-to-end Phase-1 verification suite + golden test vectors.
//!
//! Exercises the full issue → grant → delegate → attenuate → verify flow
//! against the REAL crypto layer (ed25519-dalek) and the REAL wire codec,
//! including the negative cases the threat model cares about (chain
//! splice, wrong key, tampered payload, claim mismatch, unknown
//! principal).
//!
//! The same tokens are pinned as golden vectors in
//! `test-vectors/phase1-vectors.json` (repo root). Regenerate with
//! `DLC_BLESS=1 cargo test -p dlc-verifier --test end_to_end`.

use dlc_core::judgment::{KeyRing, TypingProblem};
use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
use dlc_core::syntax::{Prop, Signature, Term};
use dlc_core::time::TimeBound;
use dlc_crypto::ed25519;
use dlc_protocol::wire;
use dlc_verifier::check::{verify, verify_with_assumptions};
use dlc_verifier::VerifyResult;

const SEED_A: [u8; 32] = [0xaa; 32];
const SEED_B: [u8; 32] = [0xbb; 32];
const SEED_C: [u8; 32] = [0xcc; 32];
const EPOCH_MS: u64 = 1_750_000_000_000;

struct Party {
    seed: [u8; 32],
    principal: Principal,
    pid: [u8; 32],
    pk: [u8; 32],
}

fn party(seed: [u8; 32]) -> Party {
    let pk = ed25519::public_key(&seed);
    let pid = dlc_crypto::principal_id(&pk);
    Party {
        seed,
        principal: Principal::Atom(PrincipalId(pid)),
        pid,
        pk,
    }
}

fn keyring(parties: &[&Party]) -> KeyRing {
    KeyRing {
        entries: parties
            .iter()
            .map(|p| KeyRecord {
                principal: PrincipalId(p.pid),
                alg: ed25519::ALG_ED25519,
                public_key: p.pk.to_vec(),
            })
            .collect(),
    }
}

fn sign_over(p: &Party, inner: Term) -> Term {
    let canonical = wire::canonical_bytes(&inner);
    let sig = ed25519::sign(&p.seed, &canonical);
    Term::Sign(
        p.principal.clone(),
        Box::new(inner),
        Signature {
            alg: ed25519::ALG_ED25519,
            bytes: sig.to_vec(),
        },
    )
}

/// B's issued token: `Sign(B, Now, sig) : B says ⊤`.
fn issued(b: &Party) -> Term {
    sign_over(b, Term::Now(TimeBound { epoch_ms: EPOCH_MS }))
}

/// A's grant: `Sign(A, Var 0, sig)`, meaningful under the assumption
/// `speaksFor(B, A)` at context slot 0.
fn grant(a: &Party) -> Term {
    sign_over(a, Term::Var(0))
}

/// The full chain: `Attenuate(Delegate(grant_A, issued_B), ⊤)`.
fn full_chain(a: &Party, b: &Party) -> Term {
    let d = Term::Delegate(Box::new(grant(a)), Box::new(issued(b)));
    Term::Attenuate(Box::new(d), Box::new(Prop::Top))
}

fn says(p: &Party, inner: Prop) -> Prop {
    Prop::Says(p.principal.clone(), Box::new(inner))
}

fn says_acting(a: &Party, b: &Party, inner: Prop) -> Prop {
    Prop::Says(
        Principal::Acting(Box::new(a.principal.clone()), Box::new(b.principal.clone())),
        Box::new(inner),
    )
}

fn speaks_for(q: &Party, p: &Party) -> Prop {
    Prop::SpeaksFor(q.principal.clone(), p.principal.clone())
}

fn assert_ok(r: VerifyResult) {
    match r {
        VerifyResult::Ok => {}
        VerifyResult::Fail { reason, .. } => panic!("expected Ok, got Fail: {reason}"),
    }
}

fn assert_fail_containing(r: VerifyResult, needle: &str) {
    match r {
        VerifyResult::Ok => panic!("expected Fail containing {needle:?}, got Ok"),
        VerifyResult::Fail { reason, .. } => {
            assert!(
                reason.contains(needle),
                "expected failure reason containing {needle:?}, got: {reason}"
            );
        }
    }
}

// ---------------------------------------------------------------- positive

#[test]
fn issued_token_verifies() {
    let b = party(SEED_B);
    let token = wire::encode(&issued(&b));
    assert_ok(verify(&token, &says(&b, Prop::Top), &keyring(&[&b])));
}

#[test]
fn full_chain_verifies_under_assumption() {
    let (a, b) = (party(SEED_A), party(SEED_B));
    let token = wire::encode(&full_chain(&a, &b));
    assert_ok(verify_with_assumptions(
        &token,
        &says_acting(&a, &b, Prop::Top),
        &keyring(&[&a, &b]),
        &[speaks_for(&b, &a)],
    ));
}

// ---------------------------------------------------------------- negative

#[test]
fn wrong_key_rejected() {
    let (a, b) = (party(SEED_A), party(SEED_B));
    let token = wire::encode(&issued(&b));
    // Keyring maps B's principal id to A's public key.
    let bad_keyring = KeyRing {
        entries: vec![KeyRecord {
            principal: PrincipalId(b.pid),
            alg: ed25519::ALG_ED25519,
            public_key: a.pk.to_vec(),
        }],
    };
    assert_fail_containing(
        verify(&token, &says(&b, Prop::Top), &bad_keyring),
        "signature",
    );
}

#[test]
fn unknown_principal_rejected() {
    let b = party(SEED_B);
    let token = wire::encode(&issued(&b));
    assert_fail_containing(
        verify(&token, &says(&b, Prop::Top), &KeyRing::default()),
        "signature check failed",
    );
}

#[test]
fn tampered_payload_rejected() {
    let b = party(SEED_B);
    // Re-sign Now(EPOCH), then swap the payload for Now(EPOCH+1): the
    // signature is over the ORIGINAL canonical bytes, so this must fail.
    let honest = issued(&b);
    let tampered = match honest {
        Term::Sign(p, _, sig) => Term::Sign(
            p,
            Box::new(Term::Now(TimeBound {
                epoch_ms: EPOCH_MS + 1,
            })),
            sig,
        ),
        _ => unreachable!(),
    };
    let token = wire::encode(&tampered);
    assert_fail_containing(
        verify(&token, &says(&b, Prop::Top), &keyring(&[&b])),
        "signature",
    );
}

#[test]
fn claim_mismatch_rejected() {
    let b = party(SEED_B);
    let token = wire::encode(&issued(&b));
    assert_fail_containing(
        verify(&token, &Prop::Top, &keyring(&[&b])),
        "logical typing",
    );
}

/// The splice: C's issued token grafted under A's grant for B. The
/// delegate rule requires the SAME principal in both premises, so the
/// chain `Delegate(grant_A[B⇒A], issued_C)` has no derivation.
#[test]
fn chain_splice_rejected() {
    let (a, b, c) = (party(SEED_A), party(SEED_B), party(SEED_C));
    let spliced = Term::Delegate(Box::new(grant(&a)), Box::new(issued(&c)));
    let token = wire::encode(&spliced);
    assert_fail_containing(
        verify_with_assumptions(
            &token,
            &says_acting(&a, &c, Prop::Top),
            &keyring(&[&a, &b, &c]),
            &[speaks_for(&b, &a)],
        ),
        "logical typing",
    );
}

/// Well-typedness alone is NOT acceptance: a forged signature on a term
/// that typechecks logically must still be rejected (the second conjunct
/// of the T2 characterization does real work).
#[test]
fn logically_typed_but_forged_signature_rejected() {
    let b = party(SEED_B);
    let inner = Term::Now(TimeBound { epoch_ms: EPOCH_MS });
    let forged = Term::Sign(
        b.principal.clone(),
        Box::new(inner.clone()),
        Signature {
            alg: ed25519::ALG_ED25519,
            bytes: vec![0u8; 64],
        },
    );
    // Logical typing succeeds…
    let problem = TypingProblem {
        ctx: Default::default(),
        term: forged.clone(),
        prop: says(&b, Prop::Top),
    };
    assert!(dlc_core::decide::decide_pure(&problem));
    // …but verification does not.
    let token = wire::encode(&forged);
    assert_fail_containing(
        verify(&token, &says(&b, Prop::Top), &keyring(&[&b])),
        "signature",
    );
}

// ------------------------------------------------------------ golden file

/// Golden vectors: hex tokens + CBOR-hex claims pinned in
/// `test-vectors/phase1-vectors.json`. `DLC_BLESS=1` regenerates.
#[test]
fn golden_vectors_match_and_verify() {
    let (a, b) = (party(SEED_A), party(SEED_B));
    let kr = keyring(&[&a, &b]);

    let entries = [
        (
            "issued-b-says-top",
            wire::encode(&issued(&b)),
            wire::encode_prop(&says(&b, Prop::Top)),
            Vec::<Prop>::new(),
            true,
        ),
        (
            "full-chain-acting-a-b",
            wire::encode(&full_chain(&a, &b)),
            wire::encode_prop(&says_acting(&a, &b, Prop::Top)),
            vec![speaks_for(&b, &a)],
            true,
        ),
        (
            "splice-c-under-grant-for-b",
            wire::encode(&Term::Delegate(
                Box::new(grant(&a)),
                Box::new(issued(&party(SEED_C))),
            )),
            wire::encode_prop(&says_acting(&a, &party(SEED_C), Prop::Top)),
            vec![speaks_for(&b, &a)],
            false,
        ),
    ];

    let mut json = String::from("{\n  \"generator\": \"cargo test -p dlc-verifier --test end_to_end (DLC_BLESS=1)\",\n  \"keyring\": [\n");
    for (i, p) in [&a, &b].iter().enumerate() {
        json.push_str(&format!(
            "    {{\"seed\": \"{}\", \"principal\": \"{}\", \"public_key\": \"{}\"}}{}\n",
            hex(&p.seed),
            hex(&p.pid),
            hex(&p.pk),
            if i == 1 { "" } else { "," }
        ));
    }
    json.push_str("  ],\n  \"vectors\": [\n");
    for (i, (name, token, claim, assumptions, expect_ok)) in entries.iter().enumerate() {
        // Every vector must actually behave as pinned.
        let result = verify_with_assumptions(token, &wire::decode_prop(claim).unwrap(), &kr, assumptions);
        match (expect_ok, &result) {
            (true, VerifyResult::Ok) => {}
            (false, VerifyResult::Fail { .. }) => {}
            _ => panic!("vector {name}: behavior does not match pinned expectation"),
        }
        json.push_str(&format!(
            "    {{\"name\": \"{}\", \"token\": \"{}\", \"claim\": \"{}\", \"expect\": \"{}\"}}{}\n",
            name,
            hex(token),
            hex(claim),
            if *expect_ok { "ok" } else { "fail" },
            if i + 1 == entries.len() { "" } else { "," }
        ));
    }
    json.push_str("  ]\n}\n");

    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../test-vectors/phase1-vectors.json");
    if std::env::var("DLC_BLESS").is_ok() {
        std::fs::create_dir_all(std::path::Path::new(path).parent().unwrap()).unwrap();
        std::fs::write(path, &json).unwrap();
    } else {
        let committed = std::fs::read_to_string(path)
            .expect("test-vectors/phase1-vectors.json missing — run with DLC_BLESS=1");
        assert_eq!(
            committed, json,
            "golden vectors drifted — if intentional, regenerate with DLC_BLESS=1"
        );
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
