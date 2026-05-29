//! cargo-fuzz target: structured fuzz of CBOR canonical round-trip.
//!
//! Property: for every well-formed `Term` value `t` the equality
//!   encode(decode(encode(t))) == encode(t)
//! holds bit-identically. This is the strong canonical-round-trip
//! property: there is exactly one wire encoding per term.
//!
//! We hand-roll `Arbitrary` over `Term`, `Prop`, `Principal`,
//! `Obligation`, `Label`, `TimeBound`, and `Signature` rather than
//! deriving it. Reason: `dlc-core` is the Aeneas translation target
//! and must remain free of third-party dependencies (no `arbitrary`,
//! no `serde`, no `derive` macros). Manual generation in the fuzz
//! target keeps that hygiene intact while still exercising every one
//! of the 22 `Term` constructors.
//!
//! Depth is bounded with a size budget to avoid stack overflow in the
//! generator -- libFuzzer would otherwise occasionally feed us a
//! recursive grammar that blows past the default 8 MiB stack.

#![no_main]

use arbitrary::{Arbitrary, Result, Unstructured};
use libfuzzer_sys::fuzz_target;

use dlc_core::ifc::Label;
use dlc_core::obligation::{ActionId, DpBudget, Obligation};
use dlc_core::principal::{Principal, PrincipalId};
use dlc_core::syntax::{Prop, Signature, Term};
use dlc_core::time::TimeBound;
use dlc_protocol::wire::{decode, encode};

/// Size budget. Each recursive call decrements by 1; when it hits zero
/// the generator picks a non-recursive constructor. Cap chosen so the
/// generated AST fits in a stack-safe depth (well under libFuzzer's
/// default).
const MAX_DEPTH: u8 = 6;

fn gen_label(u: &mut Unstructured<'_>) -> Result<Label> {
    let len = u.int_in_range::<usize>(0..=8)?;
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(u.arbitrary::<u32>()?);
    }
    Ok(Label(v))
}

fn gen_principal_id(u: &mut Unstructured<'_>) -> Result<PrincipalId> {
    let mut id = [0u8; 32];
    u.fill_buffer(&mut id)?;
    Ok(PrincipalId(id))
}

fn gen_principal(u: &mut Unstructured<'_>, depth: u8) -> Result<Principal> {
    if depth == 0 {
        return Ok(Principal::Atom(gen_principal_id(u)?));
    }
    match u.int_in_range::<u8>(0..=3)? {
        0 => Ok(Principal::Atom(gen_principal_id(u)?)),
        1 => Ok(Principal::And(
            Box::new(gen_principal(u, depth - 1)?),
            Box::new(gen_principal(u, depth - 1)?),
        )),
        2 => Ok(Principal::Or(
            Box::new(gen_principal(u, depth - 1)?),
            Box::new(gen_principal(u, depth - 1)?),
        )),
        _ => Ok(Principal::Acting(
            Box::new(gen_principal(u, depth - 1)?),
            Box::new(gen_principal(u, depth - 1)?),
        )),
    }
}

fn gen_time(u: &mut Unstructured<'_>) -> Result<TimeBound> {
    Ok(TimeBound {
        epoch_ms: u.arbitrary::<u64>()?,
    })
}

fn gen_signature(u: &mut Unstructured<'_>) -> Result<Signature> {
    let alg = u.arbitrary::<u8>()?;
    let len = u.int_in_range::<usize>(0..=128)?;
    let mut bytes = vec![0u8; len];
    u.fill_buffer(&mut bytes)?;
    Ok(Signature { alg, bytes })
}

fn gen_action_id(u: &mut Unstructured<'_>) -> Result<ActionId> {
    let len = u.int_in_range::<usize>(0..=16)?;
    let mut bytes = vec![0u8; len];
    u.fill_buffer(&mut bytes)?;
    Ok(ActionId(bytes))
}

fn gen_dp_budget(u: &mut Unstructured<'_>) -> Result<DpBudget> {
    Ok(DpBudget {
        epsilon_micros: u.arbitrary::<u64>()?,
        delta_micros: u.arbitrary::<u64>()?,
    })
}

fn gen_obligation(u: &mut Unstructured<'_>, depth: u8) -> Result<Obligation> {
    if depth == 0 {
        return Ok(Obligation::Top);
    }
    match u.int_in_range::<u8>(0..=6)? {
        0 => Ok(Obligation::Top),
        1 => Ok(Obligation::Bot),
        2 => Ok(Obligation::ActOf(
            gen_principal(u, depth - 1)?,
            gen_action_id(u)?,
        )),
        3 => Ok(Obligation::Within(gen_time(u)?)),
        4 => Ok(Obligation::Tensor(
            Box::new(gen_obligation(u, depth - 1)?),
            Box::new(gen_obligation(u, depth - 1)?),
        )),
        5 => Ok(Obligation::Lolli(
            Box::new(gen_obligation(u, depth - 1)?),
            Box::new(gen_obligation(u, depth - 1)?),
        )),
        _ => Ok(Obligation::DpBudget(gen_dp_budget(u)?)),
    }
}

fn gen_prop(u: &mut Unstructured<'_>, depth: u8) -> Result<Prop> {
    if depth == 0 {
        return Ok(Prop::Atom(u.arbitrary::<u32>()?));
    }
    match u.int_in_range::<u8>(0..=11)? {
        0 => Ok(Prop::Top),
        1 => Ok(Prop::Bot),
        2 => Ok(Prop::Atom(u.arbitrary::<u32>()?)),
        3 => Ok(Prop::Imp(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_prop(u, depth - 1)?),
        )),
        4 => Ok(Prop::And(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_prop(u, depth - 1)?),
        )),
        5 => Ok(Prop::Or(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_prop(u, depth - 1)?),
        )),
        6 => Ok(Prop::Says(
            gen_principal(u, depth - 1)?,
            Box::new(gen_prop(u, depth - 1)?),
        )),
        7 => Ok(Prop::SpeaksFor(
            gen_principal(u, depth - 1)?,
            gen_principal(u, depth - 1)?,
        )),
        8 => Ok(Prop::At(Box::new(gen_prop(u, depth - 1)?), gen_label(u)?)),
        9 => Ok(Prop::Boxed(
            gen_obligation(u, depth - 1)?,
            Box::new(gen_prop(u, depth - 1)?),
        )),
        10 => Ok(Prop::Within(
            gen_time(u)?,
            Box::new(gen_prop(u, depth - 1)?),
        )),
        _ => Ok(Prop::Tensor(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_prop(u, depth - 1)?),
        )),
    }
}

/// Generate every one of the 22 `Term` constructors, weighting variants
/// so leaf constructors are favoured when the depth budget runs out.
fn gen_term(u: &mut Unstructured<'_>, depth: u8) -> Result<Term> {
    if depth == 0 {
        return Ok(Term::Var(u.arbitrary::<u32>()?));
    }
    match u.int_in_range::<u8>(0..=21)? {
        0 => Ok(Term::Var(u.arbitrary::<u32>()?)),
        1 => Ok(Term::Lam(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        2 => Ok(Term::App(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        3 => Ok(Term::Sign(
            gen_principal(u, depth - 1)?,
            Box::new(gen_term(u, depth - 1)?),
            gen_signature(u)?,
        )),
        4 => Ok(Term::Verify(
            gen_principal(u, depth - 1)?,
            Box::new(gen_term(u, depth - 1)?),
            gen_signature(u)?,
        )),
        5 => Ok(Term::Delegate(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        6 => Ok(Term::Attenuate(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_prop(u, depth - 1)?),
        )),
        7 => Ok(Term::Discharge(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        8 => Ok(Term::LiftLabel(
            gen_label(u)?,
            Box::new(gen_term(u, depth - 1)?),
        )),
        9 => Ok(Term::Declassify(
            gen_label(u)?,
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        10 => Ok(Term::Now(gen_time(u)?)),
        11 => Ok(Term::WithinIntro(
            gen_time(u)?,
            Box::new(gen_term(u, depth - 1)?),
        )),
        12 => Ok(Term::Pair(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        13 => Ok(Term::Fst(Box::new(gen_term(u, depth - 1)?))),
        14 => Ok(Term::Snd(Box::new(gen_term(u, depth - 1)?))),
        15 => Ok(Term::Inl(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        16 => Ok(Term::Inr(
            Box::new(gen_prop(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        17 => Ok(Term::Case(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        18 => Ok(Term::TensorIntro(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        19 => Ok(Term::LetTensor(
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        20 => Ok(Term::LetSays(
            gen_principal(u, depth - 1)?,
            Box::new(gen_term(u, depth - 1)?),
            Box::new(gen_term(u, depth - 1)?),
        )),
        _ => Ok(Term::SfExtract(Box::new(gen_term(u, depth - 1)?))),
    }
}

/// Wrapper so libfuzzer-sys's `Arbitrary` trait bound is satisfied.
/// `Debug` is required by `fuzz_target!`'s macro expansion for
/// crash-reproducer printing; `Term` already derives `Debug`.
#[derive(Debug)]
struct FuzzTerm(Term);

impl<'a> Arbitrary<'a> for FuzzTerm {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(FuzzTerm(gen_term(u, MAX_DEPTH)?))
    }
}

fuzz_target!(|input: FuzzTerm| {
    let t = input.0;
    let b1 = encode(&t);
    // Property 1: any encoded term decodes successfully.
    let t2 = match decode(&b1) {
        Ok(t) => t,
        Err(e) => panic!("decode of well-formed encoding failed: {e:?}"),
    };
    // Property 2: round-trip preserves the term (semantic equality).
    assert_eq!(t, t2, "decode != original");
    // Property 3: re-encode is bit-identical (canonical CBOR).
    let b2 = encode(&t2);
    assert_eq!(b1, b2, "re-encode produced different bytes");
});
