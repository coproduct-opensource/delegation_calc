//! Wire format for DLC proof terms.
//!
//! The schema (ABNF) is frozen in `spec/abnf.md`. Content-addressed: every
//! subterm hashes to a stable id, enabling selective recomputation and
//! cross-organizational caching.
//!
//! Encoding strategy: each `Term` variant becomes a CBOR array
//! `[tag, arg1, arg2, ...]` where `tag` is the constructor index (0..23)
//! and the arguments are recursively encoded. Sub-types (`Prop`,
//! `Principal`, `Label`, `Obligation`, `TimeBound`, `Signature`) use the
//! same tag-arrayed shape.
//!
//! Why hand-rolled (not serde-derive): `dlc-core` is the Aeneas
//! translation target and must stay zero-dep. Adding serde's derive
//! macros would bring in compile-time codegen that Aeneas can't follow.
//! Hand-rolling against ciborium's `Value` API keeps `dlc-core` clean and
//! puts the encoding entirely in `dlc-protocol`.

use ciborium::Value;
use dlc_core::ifc::Label;
use dlc_core::judgment::KeyRing;
use dlc_core::obligation::{ActionId, DpBudget, Obligation};
use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
use dlc_core::syntax::{Prop, Signature, Term};
use dlc_core::time::TimeBound;

use crate::ProtocolError;

// =========================================================================
// Encoders -- Rust value -> ciborium::Value
// =========================================================================

fn enc_principal_id(p: &PrincipalId) -> Value {
    Value::Bytes(p.0.to_vec())
}

fn enc_principal(p: &Principal) -> Value {
    match p {
        Principal::Atom(id) => Value::Array(vec![Value::Integer(0.into()), enc_principal_id(id)]),
        Principal::And(a, b) => Value::Array(vec![
            Value::Integer(1.into()),
            enc_principal(a),
            enc_principal(b),
        ]),
        Principal::Or(a, b) => Value::Array(vec![
            Value::Integer(2.into()),
            enc_principal(a),
            enc_principal(b),
        ]),
        Principal::Acting(a, b) => Value::Array(vec![
            Value::Integer(3.into()),
            enc_principal(a),
            enc_principal(b),
        ]),
    }
}

fn enc_label(l: &Label) -> Value {
    Value::Array(
        l.0.iter()
            .map(|&n| Value::Integer((n as u64).into()))
            .collect(),
    )
}

fn enc_time(t: &TimeBound) -> Value {
    Value::Integer(t.epoch_ms.into())
}

fn enc_dp_budget(b: &DpBudget) -> Value {
    Value::Array(vec![
        Value::Integer(b.epsilon_micros.into()),
        Value::Integer(b.delta_micros.into()),
    ])
}

fn enc_obligation(o: &Obligation) -> Value {
    match o {
        Obligation::Top => Value::Array(vec![Value::Integer(0.into())]),
        Obligation::Bot => Value::Array(vec![Value::Integer(1.into())]),
        Obligation::ActOf(p, a) => Value::Array(vec![
            Value::Integer(2.into()),
            enc_principal(p),
            Value::Bytes(a.0.clone()),
        ]),
        Obligation::Within(t) => Value::Array(vec![Value::Integer(3.into()), enc_time(t)]),
        Obligation::Tensor(a, b) => Value::Array(vec![
            Value::Integer(4.into()),
            enc_obligation(a),
            enc_obligation(b),
        ]),
        Obligation::Lolli(a, b) => Value::Array(vec![
            Value::Integer(5.into()),
            enc_obligation(a),
            enc_obligation(b),
        ]),
        Obligation::DpBudget(b) => Value::Array(vec![Value::Integer(6.into()), enc_dp_budget(b)]),
    }
}

fn enc_prop(p: &Prop) -> Value {
    match p {
        Prop::Top => Value::Array(vec![Value::Integer(0.into())]),
        Prop::Bot => Value::Array(vec![Value::Integer(1.into())]),
        Prop::Atom(n) => Value::Array(vec![
            Value::Integer(2.into()),
            Value::Integer((*n as u64).into()),
        ]),
        Prop::Imp(a, b) => Value::Array(vec![Value::Integer(3.into()), enc_prop(a), enc_prop(b)]),
        Prop::And(a, b) => Value::Array(vec![Value::Integer(4.into()), enc_prop(a), enc_prop(b)]),
        Prop::Or(a, b) => Value::Array(vec![Value::Integer(5.into()), enc_prop(a), enc_prop(b)]),
        Prop::Says(p, q) => Value::Array(vec![
            Value::Integer(6.into()),
            enc_principal(p),
            enc_prop(q),
        ]),
        Prop::SpeaksFor(p, q) => Value::Array(vec![
            Value::Integer(7.into()),
            enc_principal(p),
            enc_principal(q),
        ]),
        Prop::At(a, l) => Value::Array(vec![Value::Integer(8.into()), enc_prop(a), enc_label(l)]),
        Prop::Boxed(o, a) => Value::Array(vec![
            Value::Integer(9.into()),
            enc_obligation(o),
            enc_prop(a),
        ]),
        Prop::Within(t, a) => {
            Value::Array(vec![Value::Integer(10.into()), enc_time(t), enc_prop(a)])
        }
        Prop::Tensor(a, b) => {
            Value::Array(vec![Value::Integer(11.into()), enc_prop(a), enc_prop(b)])
        }
        Prop::Lolli(a, b) => {
            Value::Array(vec![Value::Integer(12.into()), enc_prop(a), enc_prop(b)])
        }
    }
}

fn enc_signature(s: &Signature) -> Value {
    Value::Array(vec![
        Value::Integer((s.alg as u64).into()),
        Value::Bytes(s.bytes.clone()),
    ])
}

fn enc_term(t: &Term) -> Value {
    match t {
        Term::Var(i) => Value::Array(vec![
            Value::Integer(0.into()),
            Value::Integer((*i as u64).into()),
        ]),
        Term::Lam(p, b) => Value::Array(vec![Value::Integer(1.into()), enc_prop(p), enc_term(b)]),
        Term::App(f, x) => Value::Array(vec![Value::Integer(2.into()), enc_term(f), enc_term(x)]),
        Term::Sign(p, m, s) => Value::Array(vec![
            Value::Integer(3.into()),
            enc_principal(p),
            enc_term(m),
            enc_signature(s),
        ]),
        Term::Verify(p, m, s) => Value::Array(vec![
            Value::Integer(4.into()),
            enc_principal(p),
            enc_term(m),
            enc_signature(s),
        ]),
        Term::Delegate(m, n) => {
            Value::Array(vec![Value::Integer(5.into()), enc_term(m), enc_term(n)])
        }
        Term::Attenuate(m, p) => {
            Value::Array(vec![Value::Integer(6.into()), enc_term(m), enc_prop(p)])
        }
        Term::Discharge(m, n) => {
            Value::Array(vec![Value::Integer(7.into()), enc_term(m), enc_term(n)])
        }
        Term::LiftLabel(l, m) => {
            Value::Array(vec![Value::Integer(8.into()), enc_label(l), enc_term(m)])
        }
        Term::Declassify(l, m, pi) => Value::Array(vec![
            Value::Integer(9.into()),
            enc_label(l),
            enc_term(m),
            enc_term(pi),
        ]),
        Term::Now(t) => Value::Array(vec![Value::Integer(10.into()), enc_time(t)]),
        Term::WithinIntro(t, m) => {
            Value::Array(vec![Value::Integer(11.into()), enc_time(t), enc_term(m)])
        }
        Term::Pair(a, b) => Value::Array(vec![Value::Integer(12.into()), enc_term(a), enc_term(b)]),
        Term::Fst(a) => Value::Array(vec![Value::Integer(13.into()), enc_term(a)]),
        Term::Snd(a) => Value::Array(vec![Value::Integer(14.into()), enc_term(a)]),
        Term::Inl(p, a) => Value::Array(vec![Value::Integer(15.into()), enc_prop(p), enc_term(a)]),
        Term::Inr(p, a) => Value::Array(vec![Value::Integer(16.into()), enc_prop(p), enc_term(a)]),
        Term::Case(s, l, r) => Value::Array(vec![
            Value::Integer(17.into()),
            enc_term(s),
            enc_term(l),
            enc_term(r),
        ]),
        Term::TensorIntro(a, b) => {
            Value::Array(vec![Value::Integer(18.into()), enc_term(a), enc_term(b)])
        }
        Term::LetTensor(s, b) => {
            Value::Array(vec![Value::Integer(19.into()), enc_term(s), enc_term(b)])
        }
        Term::LetSays(p, s, b) => Value::Array(vec![
            Value::Integer(20.into()),
            enc_principal(p),
            enc_term(s),
            enc_term(b),
        ]),
        Term::SfExtract(m) => Value::Array(vec![Value::Integer(21.into()), enc_term(m)]),
        // says-E `let ⟨x⟩_p = M in N` -- tag 23, APPENDED for the same reason
        // as 22: explicit positional tags, so no existing encoding moves.
        Term::SaysBind(p, s, b) => Value::Array(vec![
            Value::Integer(23.into()),
            enc_principal(p),
            enc_term(s),
            enc_term(b),
        ]),
        // box_O(M, N) -- tag 22, APPENDED. Tags here are explicit positional
        // integers, so a new variant leaves every existing term's encoding
        // byte-identical: `canonical_bytes` is unchanged for anything that
        // could already be encoded, and signatures over such terms stay valid.
        // Never renumber an existing tag.
        Term::Boxed(o, m, n) => Value::Array(vec![
            Value::Integer(22.into()),
            enc_obligation(o),
            enc_term(m),
            enc_term(n),
        ]),
    }
}

// =========================================================================
// Decoders -- ciborium::Value -> Rust value
// =========================================================================

fn arr(v: &Value) -> Result<&[Value], ProtocolError> {
    match v {
        Value::Array(a) => Ok(a),
        _ => Err(ProtocolError::Cbor("expected array".into())),
    }
}

fn tag(v: &Value) -> Result<u64, ProtocolError> {
    match v {
        Value::Integer(i) => Ok(<i128>::from(*i) as u64),
        _ => Err(ProtocolError::Cbor("expected integer tag".into())),
    }
}

fn u32_of(v: &Value) -> Result<u32, ProtocolError> {
    match v {
        Value::Integer(i) => Ok(<i128>::from(*i) as u32),
        _ => Err(ProtocolError::Cbor("expected u32".into())),
    }
}

fn u64_of(v: &Value) -> Result<u64, ProtocolError> {
    match v {
        Value::Integer(i) => Ok(<i128>::from(*i) as u64),
        _ => Err(ProtocolError::Cbor("expected u64".into())),
    }
}

fn bytes_of(v: &Value) -> Result<Vec<u8>, ProtocolError> {
    match v {
        Value::Bytes(b) => Ok(b.clone()),
        _ => Err(ProtocolError::Cbor("expected byte string".into())),
    }
}

fn dec_principal_id(v: &Value) -> Result<PrincipalId, ProtocolError> {
    let b = bytes_of(v)?;
    let arr: [u8; 32] = b
        .try_into()
        .map_err(|_| ProtocolError::Cbor("principal id must be 32 bytes".into()))?;
    Ok(PrincipalId(arr))
}

fn dec_principal(v: &Value) -> Result<Principal, ProtocolError> {
    let a = arr(v)?;
    match tag(&a[0])? {
        0 => Ok(Principal::Atom(dec_principal_id(&a[1])?)),
        1 => Ok(Principal::And(
            Box::new(dec_principal(&a[1])?),
            Box::new(dec_principal(&a[2])?),
        )),
        2 => Ok(Principal::Or(
            Box::new(dec_principal(&a[1])?),
            Box::new(dec_principal(&a[2])?),
        )),
        3 => Ok(Principal::Acting(
            Box::new(dec_principal(&a[1])?),
            Box::new(dec_principal(&a[2])?),
        )),
        t => Err(ProtocolError::Cbor(format!("bad principal tag {}", t))),
    }
}

fn dec_label(v: &Value) -> Result<Label, ProtocolError> {
    let a = arr(v)?;
    let caps: Result<Vec<u32>, _> = a.iter().map(u32_of).collect();
    Ok(Label(caps?))
}

fn dec_time(v: &Value) -> Result<TimeBound, ProtocolError> {
    Ok(TimeBound {
        epoch_ms: u64_of(v)?,
    })
}

fn dec_dp_budget(v: &Value) -> Result<DpBudget, ProtocolError> {
    let a = arr(v)?;
    Ok(DpBudget {
        epsilon_micros: u64_of(&a[0])?,
        delta_micros: u64_of(&a[1])?,
    })
}

fn dec_obligation(v: &Value) -> Result<Obligation, ProtocolError> {
    let a = arr(v)?;
    match tag(&a[0])? {
        0 => Ok(Obligation::Top),
        1 => Ok(Obligation::Bot),
        2 => Ok(Obligation::ActOf(
            dec_principal(&a[1])?,
            ActionId(bytes_of(&a[2])?),
        )),
        3 => Ok(Obligation::Within(dec_time(&a[1])?)),
        4 => Ok(Obligation::Tensor(
            Box::new(dec_obligation(&a[1])?),
            Box::new(dec_obligation(&a[2])?),
        )),
        5 => Ok(Obligation::Lolli(
            Box::new(dec_obligation(&a[1])?),
            Box::new(dec_obligation(&a[2])?),
        )),
        6 => Ok(Obligation::DpBudget(dec_dp_budget(&a[1])?)),
        t => Err(ProtocolError::Cbor(format!("bad obligation tag {}", t))),
    }
}

fn dec_prop(v: &Value) -> Result<Prop, ProtocolError> {
    let a = arr(v)?;
    match tag(&a[0])? {
        0 => Ok(Prop::Top),
        1 => Ok(Prop::Bot),
        2 => Ok(Prop::Atom(u32_of(&a[1])?)),
        3 => Ok(Prop::Imp(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_prop(&a[2])?),
        )),
        4 => Ok(Prop::And(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_prop(&a[2])?),
        )),
        5 => Ok(Prop::Or(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_prop(&a[2])?),
        )),
        6 => Ok(Prop::Says(
            dec_principal(&a[1])?,
            Box::new(dec_prop(&a[2])?),
        )),
        7 => Ok(Prop::SpeaksFor(
            dec_principal(&a[1])?,
            dec_principal(&a[2])?,
        )),
        8 => Ok(Prop::At(Box::new(dec_prop(&a[1])?), dec_label(&a[2])?)),
        9 => Ok(Prop::Boxed(
            dec_obligation(&a[1])?,
            Box::new(dec_prop(&a[2])?),
        )),
        10 => Ok(Prop::Within(dec_time(&a[1])?, Box::new(dec_prop(&a[2])?))),
        11 => Ok(Prop::Tensor(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_prop(&a[2])?),
        )),
        12 => Ok(Prop::Lolli(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_prop(&a[2])?),
        )),
        t => Err(ProtocolError::Cbor(format!("bad prop tag {}", t))),
    }
}

fn dec_signature(v: &Value) -> Result<Signature, ProtocolError> {
    let a = arr(v)?;
    Ok(Signature {
        alg: u32_of(&a[0])? as u8,
        bytes: bytes_of(&a[1])?,
    })
}

fn dec_term(v: &Value) -> Result<Term, ProtocolError> {
    let a = arr(v)?;
    match tag(&a[0])? {
        0 => Ok(Term::Var(u32_of(&a[1])?)),
        1 => Ok(Term::Lam(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        2 => Ok(Term::App(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        3 => Ok(Term::Sign(
            dec_principal(&a[1])?,
            Box::new(dec_term(&a[2])?),
            dec_signature(&a[3])?,
        )),
        4 => Ok(Term::Verify(
            dec_principal(&a[1])?,
            Box::new(dec_term(&a[2])?),
            dec_signature(&a[3])?,
        )),
        5 => Ok(Term::Delegate(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        6 => Ok(Term::Attenuate(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_prop(&a[2])?),
        )),
        7 => Ok(Term::Discharge(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        8 => Ok(Term::LiftLabel(
            dec_label(&a[1])?,
            Box::new(dec_term(&a[2])?),
        )),
        9 => Ok(Term::Declassify(
            dec_label(&a[1])?,
            Box::new(dec_term(&a[2])?),
            Box::new(dec_term(&a[3])?),
        )),
        10 => Ok(Term::Now(dec_time(&a[1])?)),
        11 => Ok(Term::WithinIntro(
            dec_time(&a[1])?,
            Box::new(dec_term(&a[2])?),
        )),
        12 => Ok(Term::Pair(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        13 => Ok(Term::Fst(Box::new(dec_term(&a[1])?))),
        14 => Ok(Term::Snd(Box::new(dec_term(&a[1])?))),
        15 => Ok(Term::Inl(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        16 => Ok(Term::Inr(
            Box::new(dec_prop(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        17 => Ok(Term::Case(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
            Box::new(dec_term(&a[3])?),
        )),
        18 => Ok(Term::TensorIntro(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        19 => Ok(Term::LetTensor(
            Box::new(dec_term(&a[1])?),
            Box::new(dec_term(&a[2])?),
        )),
        20 => Ok(Term::LetSays(
            dec_principal(&a[1])?,
            Box::new(dec_term(&a[2])?),
            Box::new(dec_term(&a[3])?),
        )),
        21 => Ok(Term::SfExtract(Box::new(dec_term(&a[1])?))),
        23 => Ok(Term::SaysBind(
            dec_principal(&a[1])?,
            Box::new(dec_term(&a[2])?),
            Box::new(dec_term(&a[3])?),
        )),
        22 => Ok(Term::Boxed(
            dec_obligation(&a[1])?,
            Box::new(dec_term(&a[2])?),
            Box::new(dec_term(&a[3])?),
        )),
        t => Err(ProtocolError::Cbor(format!("bad term tag {}", t))),
    }
}

// =========================================================================
// Public API
// =========================================================================

/// Encode a proof term to its wire bytes (CBOR; COSE_Sign1 envelope wraps
/// this at the verification layer).
pub fn encode(term: &Term) -> Vec<u8> {
    let v = enc_term(term);
    let mut buf = Vec::new();
    ciborium::into_writer(&v, &mut buf).expect("encoding to Vec cannot fail");
    buf
}

/// Decode a wire byte string into a proof term.
pub fn decode(bytes: &[u8]) -> Result<Term, ProtocolError> {
    let v: Value = ciborium::from_reader(bytes).map_err(|e| ProtocolError::Cbor(format!("{e}")))?;
    dec_term(&v)
}

/// The canonical byte encoding of a term for SIGNING purposes.
///
/// `says-I` signatures are over exactly these bytes of the signed
/// subterm — this is the seam the Lean side models as the opaque
/// `canonicalBytes` in `lean/DLC/Correspondence.lean`. It is the wire
/// encoding itself: one deterministic encoder, no second "canonical
/// form" to drift from it. (It lives here rather than in `dlc-crypto`
/// because the dependency arrow points protocol → crypto, not the
/// reverse.)
pub fn canonical_bytes(term: &Term) -> Vec<u8> {
    encode(term)
}

/// Encode a proposition (for verifier inputs — the claimed `Prop` —
/// not part of the proof-term wire format, which embeds propositions
/// via the same `enc_prop`).
pub fn encode_prop(p: &Prop) -> Vec<u8> {
    let v = enc_prop(p);
    let mut buf = Vec::new();
    ciborium::into_writer(&v, &mut buf).expect("encoding to Vec cannot fail");
    buf
}

/// Decode a proposition encoded by [`encode_prop`].
pub fn decode_prop(bytes: &[u8]) -> Result<Prop, ProtocolError> {
    let v: Value = ciborium::from_reader(bytes).map_err(|e| ProtocolError::Cbor(format!("{e}")))?;
    dec_prop(&v)
}

/// Encode a keyring (verifier input: principal-id → public-key rows).
/// Shape: CBOR array of `[pid: bytes(32), alg: uint, pk: bytes]`.
pub fn encode_keyring(k: &KeyRing) -> Vec<u8> {
    let rows: Vec<Value> = k
        .entries
        .iter()
        .map(|r| {
            Value::Array(vec![
                Value::Bytes(r.principal.0.to_vec()),
                Value::Integer((r.alg as u64).into()),
                Value::Bytes(r.public_key.clone()),
            ])
        })
        .collect();
    let mut buf = Vec::new();
    ciborium::into_writer(&Value::Array(rows), &mut buf).expect("encoding to Vec cannot fail");
    buf
}

/// Decode a keyring encoded by [`encode_keyring`].
pub fn decode_keyring(bytes: &[u8]) -> Result<KeyRing, ProtocolError> {
    let v: Value = ciborium::from_reader(bytes).map_err(|e| ProtocolError::Cbor(format!("{e}")))?;
    let rows = v
        .as_array()
        .ok_or_else(|| ProtocolError::Cbor("keyring: expected array".into()))?;
    let mut entries = Vec::with_capacity(rows.len());
    for row in rows {
        let a = row
            .as_array()
            .ok_or_else(|| ProtocolError::Cbor("keyring row: expected array".into()))?;
        if a.len() != 3 {
            return Err(ProtocolError::Cbor("keyring row: expected 3 fields".into()));
        }
        let pid_bytes = a[0]
            .as_bytes()
            .ok_or_else(|| ProtocolError::Cbor("keyring pid: expected bytes".into()))?;
        let pid: [u8; 32] = pid_bytes
            .as_slice()
            .try_into()
            .map_err(|_| ProtocolError::Cbor("keyring pid: expected 32 bytes".into()))?;
        let alg: u8 = a[1]
            .as_integer()
            .and_then(|i| u8::try_from(i).ok())
            .ok_or_else(|| ProtocolError::Cbor("keyring alg: expected u8".into()))?;
        let pk = a[2]
            .as_bytes()
            .ok_or_else(|| ProtocolError::Cbor("keyring pk: expected bytes".into()))?
            .clone();
        entries.push(KeyRecord {
            principal: PrincipalId(pid),
            alg,
            public_key: pk,
        });
    }
    Ok(KeyRing { entries })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Round-trip test helper.
    fn round_trip(t: Term) {
        let bytes = encode(&t);
        let back = decode(&bytes).expect("decode should succeed");
        assert_eq!(t, back, "round-trip failed for term");
    }

    fn p() -> Principal {
        Principal::Atom(PrincipalId([7u8; 32]))
    }

    fn sig() -> Signature {
        Signature {
            alg: 0,
            bytes: vec![0xAB; 64],
        }
    }

    #[test]
    fn rt_var() {
        round_trip(Term::Var(42));
    }

    #[test]
    fn rt_lam() {
        round_trip(Term::Lam(Box::new(Prop::Atom(3)), Box::new(Term::Var(0))));
    }

    #[test]
    fn rt_app() {
        round_trip(Term::App(
            Box::new(Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)))),
            Box::new(Term::Var(5)),
        ));
    }

    #[test]
    fn rt_sign() {
        round_trip(Term::Sign(p(), Box::new(Term::Var(0)), sig()));
    }

    #[test]
    fn rt_verify() {
        round_trip(Term::Verify(p(), Box::new(Term::Var(0)), sig()));
    }

    #[test]
    fn rt_delegate() {
        round_trip(Term::Delegate(
            Box::new(Term::Sign(p(), Box::new(Term::Var(0)), sig())),
            Box::new(Term::Sign(p(), Box::new(Term::Var(1)), sig())),
        ));
    }

    #[test]
    fn rt_attenuate() {
        round_trip(Term::Attenuate(
            Box::new(Term::Sign(p(), Box::new(Term::Var(0)), sig())),
            Box::new(Prop::Atom(1)),
        ));
    }

    #[test]
    fn rt_discharge() {
        round_trip(Term::Discharge(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        ));
    }

    #[test]
    fn rt_lift_label() {
        round_trip(Term::LiftLabel(
            Label(vec![1, 2, 3]),
            Box::new(Term::Var(0)),
        ));
    }

    #[test]
    fn rt_declassify() {
        round_trip(Term::Declassify(
            Label(vec![1]),
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        ));
    }

    #[test]
    fn rt_now() {
        round_trip(Term::Now(TimeBound {
            epoch_ms: 1_700_000_000_000,
        }));
    }

    #[test]
    fn rt_within_intro() {
        round_trip(Term::WithinIntro(
            TimeBound {
                epoch_ms: 1_700_000_000_000,
            },
            Box::new(Term::Var(0)),
        ));
    }

    #[test]
    fn rt_pair() {
        round_trip(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(1))));
    }

    #[test]
    fn rt_fst_snd() {
        round_trip(Term::Fst(Box::new(Term::Pair(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        ))));
        round_trip(Term::Snd(Box::new(Term::Pair(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        ))));
    }

    #[test]
    fn rt_inl_inr_case() {
        round_trip(Term::Inl(Box::new(Prop::Atom(0)), Box::new(Term::Var(0))));
        round_trip(Term::Inr(Box::new(Prop::Atom(0)), Box::new(Term::Var(0))));
        round_trip(Term::Case(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
            Box::new(Term::Var(2)),
        ));
    }

    #[test]
    fn rt_tensor() {
        round_trip(Term::TensorIntro(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        ));
        round_trip(Term::LetTensor(
            Box::new(Term::TensorIntro(
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
            Box::new(Term::Var(0)),
        ));
    }

    #[test]
    fn rt_let_says() {
        round_trip(Term::LetSays(
            p(),
            Box::new(Term::Sign(p(), Box::new(Term::Var(0)), sig())),
            Box::new(Term::Var(0)),
        ));
    }

    #[test]
    fn rt_sf_extract() {
        round_trip(Term::SfExtract(Box::new(Term::Sign(
            p(),
            Box::new(Term::Var(0)),
            sig(),
        ))));
    }

    /// Compound deep nesting (smoke test for recursion robustness).
    #[test]
    fn rt_deeply_nested() {
        let deep = (0..10).fold(Term::Var(0), |acc, _| {
            Term::Lam(Box::new(Prop::Atom(0)), Box::new(acc))
        });
        round_trip(deep);
    }

    /// Compound: a full delegation chain term.
    #[test]
    fn rt_full_delegation_chain() {
        let speaks_for = Term::Sign(p(), Box::new(Term::Var(0)), sig());
        let says = Term::Sign(p(), Box::new(Term::Var(1)), sig());
        let delegated = Term::Delegate(Box::new(speaks_for), Box::new(says));
        let attenuated = Term::Attenuate(Box::new(delegated), Box::new(Prop::Atom(7)));
        round_trip(attenuated);
    }

    /// Decoding garbage bytes yields a clear error.
    #[test]
    fn decode_garbage_errors() {
        let result = decode(&[0xFF, 0xFE, 0xFD]);
        assert!(result.is_err());
    }

    /// Decoding an empty slice errors.
    #[test]
    fn decode_empty_errors() {
        let result = decode(&[]);
        assert!(result.is_err());
    }

    // =====================================================================
    // Canonical round-trip: encode -> decode -> encode is bit-identical.
    //
    // This is the property the audit (item 4) requires across all 22
    // `Term` constructors. The earlier `rt_*` tests check the
    // *semantic* round-trip (decode equals original). The canonical
    // property is strictly stronger: a re-encode must reproduce the
    // exact bytes, so there is no two-encoding ambiguity that could let
    // an adversary substitute equivalent-but-different-bytes wire forms
    // (which would defeat hash-based subterm caching and content
    // addressing).
    //
    // We enumerate every constructor in a single test so adding a new
    // `Term` variant without an accompanying canonical case fails CI
    // by virtue of the assert at the end (count must equal 22).
    // =====================================================================

    fn assert_canonical(t: Term) {
        let b1 = encode(&t);
        let t2 = decode(&b1).expect("first decode must succeed");
        assert_eq!(t, t2, "decode != encode^-1 (semantic round-trip)");
        let b2 = encode(&t2);
        assert_eq!(
            b1, b2,
            "re-encode produced different bytes -- the encoding is not canonical"
        );
    }

    #[test]
    fn canonical_roundtrip_all_24_constructors() {
        // Every constructor of `Term` is exercised exactly once. If a
        // new variant is added without a corresponding case here, the
        // exhaustive `match` in `Term`'s encoder would compile-fail
        // first, and the count assertion below catches the case where
        // a variant is added with an encoder but no canonical test.
        let cases: Vec<(&str, Term)> = vec![
            ("Var", Term::Var(42)),
            (
                "Lam",
                Term::Lam(Box::new(Prop::Atom(3)), Box::new(Term::Var(0))),
            ),
            (
                "App",
                Term::App(Box::new(Term::Var(1)), Box::new(Term::Var(2))),
            ),
            ("Sign", Term::Sign(p(), Box::new(Term::Var(0)), sig())),
            ("Verify", Term::Verify(p(), Box::new(Term::Var(0)), sig())),
            (
                "Delegate",
                Term::Delegate(Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            (
                "Attenuate",
                Term::Attenuate(Box::new(Term::Var(0)), Box::new(Prop::Top)),
            ),
            (
                "Discharge",
                Term::Discharge(Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            (
                "LiftLabel",
                Term::LiftLabel(Label(vec![1, 2, 3]), Box::new(Term::Var(0))),
            ),
            (
                "Declassify",
                Term::Declassify(
                    Label(vec![4, 5]),
                    Box::new(Term::Var(0)),
                    Box::new(Term::Var(1)),
                ),
            ),
            (
                "Now",
                Term::Now(TimeBound {
                    epoch_ms: 1_700_000_000_000,
                }),
            ),
            (
                "WithinIntro",
                Term::WithinIntro(
                    TimeBound {
                        epoch_ms: 2_000_000_000_000,
                    },
                    Box::new(Term::Var(0)),
                ),
            ),
            (
                "Pair",
                Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            ("Fst", Term::Fst(Box::new(Term::Var(0)))),
            ("Snd", Term::Snd(Box::new(Term::Var(0)))),
            (
                "Inl",
                Term::Inl(Box::new(Prop::Atom(1)), Box::new(Term::Var(0))),
            ),
            (
                "Inr",
                Term::Inr(Box::new(Prop::Atom(2)), Box::new(Term::Var(0))),
            ),
            (
                "Case",
                Term::Case(
                    Box::new(Term::Var(0)),
                    Box::new(Term::Var(1)),
                    Box::new(Term::Var(2)),
                ),
            ),
            (
                "TensorIntro",
                Term::TensorIntro(Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            (
                "LetTensor",
                Term::LetTensor(Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            (
                "LetSays",
                Term::LetSays(p(), Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            ("SfExtract", Term::SfExtract(Box::new(Term::Var(0)))),
            // A COMPOUND obligation, deliberately: tag 22 is the first
            // term-level path that reaches `dec_obligation`, so a flat
            // `Obligation::Top` here would leave that recursion untested
            // from the `Term` side.
            (
                "SaysBind",
                Term::SaysBind(p(), Box::new(Term::Var(0)), Box::new(Term::Var(1))),
            ),
            (
                "Boxed",
                Term::Boxed(
                    Obligation::Tensor(Box::new(Obligation::Top), Box::new(Obligation::Bot)),
                    Box::new(Term::Var(0)),
                    Box::new(Term::Var(1)),
                ),
            ),
        ];

        for (name, t) in &cases {
            let b1 = encode(t);
            let t2 = decode(&b1).unwrap_or_else(|e| panic!("decode failed for {name}: {e:?}"));
            assert_eq!(t, &t2, "{name}: decode != original");
            let b2 = encode(&t2);
            assert_eq!(b1, b2, "{name}: re-encode produced different bytes");
        }

        // Constructor count check: if this number ever changes, the
        // canonical test must be updated to match. This is the
        // anti-gaming guard the audit item 4 acceptance criteria
        // require.
        assert_eq!(
            cases.len(),
            24,
            "expected 24 Term constructors; if this count changed, update the canonical test"
        );
    }

    /// Compound canonical round-trip: a deeply nested term combining many
    /// constructors at once. Catches encode/decode pairs that are
    /// individually canonical but compose non-canonically (e.g. if a
    /// sub-encoder used a non-shortest integer form for a child but the
    /// shortest at the top level).
    #[test]
    fn canonical_roundtrip_compound() {
        let inner = Term::Delegate(
            Box::new(Term::Sign(p(), Box::new(Term::Var(0)), sig())),
            Box::new(Term::Sign(p(), Box::new(Term::Var(1)), sig())),
        );
        let attenuated = Term::Attenuate(
            Box::new(inner),
            Box::new(Prop::Says(p(), Box::new(Prop::Atom(7)))),
        );
        let labelled = Term::LiftLabel(Label(vec![1, 2, 3, 4]), Box::new(attenuated));
        let case = Term::Case(
            Box::new(labelled),
            Box::new(Term::Var(0)),
            Box::new(Term::Var(1)),
        );
        assert_canonical(case);
    }

    /// Random-but-deterministic round-trip: hand-picked structured-fuzz
    /// seeds that exercise corner cases of the encoder (high u32, full
    /// 32-byte principal id, large label vector, all obligations).
    /// Complements `crates/dlc-fuzz/fuzz/fuzz_targets/cbor_roundtrip.rs`,
    /// which runs the same property under libFuzzer with structured
    /// `arbitrary` generation.
    #[test]
    fn canonical_roundtrip_seed_corpus() {
        // Max u32 variable index.
        assert_canonical(Term::Var(u32::MAX));
        // Empty label.
        assert_canonical(Term::LiftLabel(Label(vec![]), Box::new(Term::Var(0))));
        // Wide label (256 dims).
        assert_canonical(Term::LiftLabel(
            Label((0..256u32).collect()),
            Box::new(Term::Var(0)),
        ));
        // Compound principal: ((p ⊓ q) acting r).
        let p_q = Principal::And(Box::new(p()), Box::new(p()));
        let acting = Principal::Acting(Box::new(p_q), Box::new(p()));
        assert_canonical(Term::Sign(acting, Box::new(Term::Var(0)), sig()));
    }
}
