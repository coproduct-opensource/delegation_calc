//! The wasm interface end-to-end: same CBOR surface JS callers use.

use dlc_core::judgment::KeyRing;
use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
use dlc_core::syntax::{Prop, Signature, Term};
use dlc_core::time::TimeBound;
use dlc_crypto::ed25519;
use dlc_protocol::wire;

#[test]
fn wasm_interface_accepts_valid_and_rejects_corrupt() {
    let seed = [0xbb_u8; 32];
    let pk = ed25519::public_key(&seed);
    let pid = dlc_crypto::principal_id(&pk);
    let principal = Principal::Atom(PrincipalId(pid));

    let inner = Term::Now(TimeBound { epoch_ms: 1_750_000_000_000 });
    let sig = ed25519::sign(&seed, &wire::canonical_bytes(&inner));
    let term = Term::Sign(
        principal.clone(),
        Box::new(inner),
        Signature { alg: ed25519::ALG_ED25519, bytes: sig.to_vec() },
    );

    let token = wire::encode(&term);
    let claimed = wire::encode_prop(&Prop::Says(principal, Box::new(Prop::Top)));
    let keyring = wire::encode_keyring(&KeyRing {
        entries: vec![KeyRecord {
            principal: PrincipalId(pid),
            alg: ed25519::ALG_ED25519,
            public_key: pk.to_vec(),
        }],
    });

    assert_eq!(dlc_verifier_wasm::verify_raw(&token, &claimed, &keyring), 1);

    let mut bad = token.clone();
    let n = bad.len();
    bad[n - 1] ^= 0x01;
    assert_eq!(dlc_verifier_wasm::verify_raw(&bad, &claimed, &keyring), 0);
}
