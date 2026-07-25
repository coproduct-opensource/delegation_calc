//! Phase-1 operational benchmark: verify latency + token size on the
//! golden-vector flow. Writes `test-vectors/bench-results.json`.
//!
//! Run: `cargo run --release -p dlc-bench --bin bench-vectors`
//!
//! HONESTY NOTES
//! * Numbers are host-specific; the JSON records the host triple and the
//!   build profile. CI publishes them for trend visibility, not as
//!   portable absolutes.
//! * Cross-format comparison (JWT HS256/EdDSA, Biscuit) is PENDING — it
//!   requires pulling those implementations into the workspace; until
//!   then this file contains DLC numbers only and says so.
//! * This is not yet the T1 complexity-bound regression (that needs the
//!   scaling fit against |M| and log |Γ|; the depth sweep below is its
//!   raw material).

use std::time::Instant;

use dlc_core::judgment::{KeyRing, TypingProblem};
use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
use dlc_core::syntax::{Prop, Signature, Term};
use dlc_core::time::TimeBound;
use dlc_crypto::ed25519;
use dlc_d::runtime::{admit, cap_atom};
use dlc_protocol::wire;
use dlc_verifier::check::{verify, verify_with_assumptions};
use dlc_verifier::VerifyResult;

const ITERS: u32 = 2_000;

fn main() {
    let seed_a = [0xaa_u8; 32];
    let seed_b = [0xbb_u8; 32];
    let (pid_a, pk_a) = ident(&seed_a);
    let (pid_b, pk_b) = ident(&seed_b);
    let pa = Principal::Atom(PrincipalId(pid_a));
    let pb = Principal::Atom(PrincipalId(pid_b));

    let keyring = KeyRing {
        entries: vec![
            KeyRecord {
                principal: PrincipalId(pid_a),
                alg: ed25519::ALG_ED25519,
                public_key: pk_a.to_vec(),
            },
            KeyRecord {
                principal: PrincipalId(pid_b),
                alg: ed25519::ALG_ED25519,
                public_key: pk_b.to_vec(),
            },
        ],
    };

    // Token 1: issued — Sign(B, Now) : B says ⊤.
    let issued = sign_over(
        &seed_b,
        &pb,
        Term::Now(TimeBound {
            epoch_ms: 1_750_000_000_000,
        }),
    );
    let issued_claim = Prop::Says(pb.clone(), Box::new(Prop::Top));

    // Token 2: full chain — Attenuate(Delegate(grant_A, issued_B), ⊤).
    let grant = sign_over(&seed_a, &pa, Term::Var(0));
    let chain = Term::Attenuate(
        Box::new(Term::Delegate(Box::new(grant), Box::new(issued.clone()))),
        Box::new(Prop::Top),
    );
    let chain_claim = Prop::Says(
        Principal::Acting(Box::new(pa.clone()), Box::new(pb.clone())),
        Box::new(Prop::Top),
    );
    let assumption = Prop::SpeaksFor(pb.clone(), pa.clone());

    let issued_wire = wire::encode(&issued);
    let chain_wire = wire::encode(&chain);

    let issued_ns = time_median(ITERS, || {
        assert!(matches!(
            verify(&issued_wire, &issued_claim, &keyring),
            VerifyResult::Ok
        ));
    });
    let chain_ns = time_median(ITERS, || {
        assert!(matches!(
            verify_with_assumptions(
                &chain_wire,
                &chain_claim,
                &keyring,
                std::slice::from_ref(&assumption)
            ),
            VerifyResult::Ok
        ));
    });
    // Logical typing alone (no signature checks) for the same chain — the
    // delta against chain_ns is the crypto conjunct's cost.
    let chain_term = wire::decode(&chain_wire).unwrap();
    let logic_ns = time_median(ITERS, || {
        let problem = TypingProblem {
            ctx: dlc_core::judgment::Ctx {
                additive: vec![assumption.clone()],
                linear: vec![],
            },
            term: chain_term.clone(),
            prop: chain_claim.clone(),
        };
        assert!(dlc_core::decide::decide_pure(&problem));
    });

    // ── Admission PEP latency (task #19) ─────────────────────────────────────
    // `dlc_d::runtime::admit` is the runtime verify-then-authorize check: one
    // real Ed25519 `verify_in_keyring` bound to the tool's FNV-1a cap atom,
    // fail-closed. The compile-time certificate already proved TYPEABILITY
    // (`admit_joint`, lean/DLC/AdmitFrag.lean); admit() re-derives NOTHING at
    // runtime — its entire cost is the signature conjunct. This is the
    // fast-path=slow-path story: the proof is not re-run per tool call.
    let ops_seed = [5u8; 32];
    let ops_pk = ed25519::public_key(&ops_seed);
    let ops = Principal::Atom(PrincipalId(ops_pk));
    let ops_keyring = KeyRing {
        entries: vec![KeyRecord {
            principal: PrincipalId(ops_pk),
            alg: ed25519::ALG_ED25519,
            public_key: ops_pk.to_vec(),
        }],
    };
    // The credential Ops signs: the domain-separated cap message for the tool
    // (identical to `runtime::cap_message`, which is private).
    let mut cap_msg = b"dlc-d/cap-invoke:".to_vec();
    cap_msg.extend_from_slice(&cap_atom("SendEmail").to_le_bytes());
    let cap_sig = Signature {
        alg: ed25519::ALG_ED25519,
        bytes: ed25519::sign(&ops_seed, &cap_msg).to_vec(),
    };
    // Sanity: the credential admits its tool (else the number below is meaningless).
    assert!(admit(&ops_keyring, &ops, "SendEmail", &cap_sig).is_ok());
    let admit_ns = time_median(ITERS, || {
        assert!(admit(&ops_keyring, &ops, "SendEmail", &cap_sig).is_ok());
    });
    // The FNV-1a tool→atom binding alone (black_box the tool name so it is not
    // constant-folded away): the "~free" half of admit's cost.
    let cap_atom_ns = time_median(ITERS, || {
        let _ = std::hint::black_box(cap_atom(std::hint::black_box("SendEmail")));
    });

    let json = format!(
        "{{\n  \"generator\": \"cargo run --release -p dlc-bench --bin bench-vectors\",\n  \"host\": \"{}\",\n  \"profile\": \"{}\",\n  \"iterations\": {ITERS},\n  \"comparison_formats\": \"PENDING — DLC numbers only; JWT/Biscuit comparison requires adding those implementations\",\n  \"results\": [\n    {{\"name\": \"issued-token\", \"token_bytes\": {}, \"verify_median_ns\": {}}},\n    {{\"name\": \"delegated-attenuated-chain\", \"token_bytes\": {}, \"verify_median_ns\": {}}},\n    {{\"name\": \"chain-logical-typing-only\", \"token_bytes\": {}, \"verify_median_ns\": {}}},\n    {{\"name\": \"admission-pep-admit\", \"note\": \"dlc_d::runtime::admit — one Ed25519 verify_in_keyring + FNV-1a cap binding, fail-closed; runtime re-derives nothing (typeability proved at compile time by admit_joint)\", \"verify_median_ns\": {}}},\n    {{\"name\": \"cap-atom-fnv1a-only\", \"note\": \"cap_atom(tool) alone — the tool->atom binding\", \"verify_median_ns\": {}}}\n  ]\n}}\n",
        std::env::consts::ARCH,
        if cfg!(debug_assertions) { "debug" } else { "release" },
        issued_wire.len(),
        issued_ns,
        chain_wire.len(),
        chain_ns,
        chain_wire.len(),
        logic_ns,
        admit_ns,
        cap_atom_ns,
    );

    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../test-vectors/bench-results.json"
    );
    std::fs::write(path, &json).expect("write bench-results.json");
    println!("{json}");
}

fn ident(seed: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
    let pk = ed25519::public_key(seed);
    (dlc_crypto::principal_id(&pk), pk)
}

fn sign_over(seed: &[u8; 32], principal: &Principal, inner: Term) -> Term {
    let canonical = wire::canonical_bytes(&inner);
    let sig = ed25519::sign(seed, &canonical);
    Term::Sign(
        principal.clone(),
        Box::new(inner),
        Signature {
            alg: ed25519::ALG_ED25519,
            bytes: sig.to_vec(),
        },
    )
}

fn time_median(iters: u32, mut f: impl FnMut()) -> u128 {
    let mut samples: Vec<u128> = (0..iters)
        .map(|_| {
            let t = Instant::now();
            f();
            t.elapsed().as_nanos()
        })
        .collect();
    samples.sort_unstable();
    samples[samples.len() / 2]
}
