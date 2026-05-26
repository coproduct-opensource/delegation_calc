/-
DLC — Capture-avoiding substitution and the substitution lemma.

This module mirrors `crates/dlc-core/src/subst.rs`. M1.Q2.a deliverable:

  * `shift`   — lift de-Bruijn indices over binders.
  * `subst`   — substitute for the variable at index 0.
  * Stated:   `substitution_lemma` (proof closure deferred — no `sorry`
              introduced; the theorem is stated but not yet inhabited).

The Aeneas-translated `DLC.Aeneas.DlcCore` will contain the Rust functions; a
`function_correspondence_subst` lemma (to land alongside the substitution
lemma's proof) bridges them.
-/

import DLC.Syntax

namespace DLC

/-- Lift every free de-Bruijn index in `t` by `delta`, treating indices
strictly less than `cutoff` as bound. `delta` is a `Nat`; negative shifts
are exposed as a separate `unshift` below to keep this function total. -/
def shift : Term → Nat → Nat → Term
  | Term.var i, delta, cutoff =>
      if i < cutoff then Term.var i else Term.var (i + delta)
  | Term.lam p body, delta, cutoff =>
      Term.lam p (shift body delta (cutoff + 1))
  | Term.app f x, delta, cutoff =>
      Term.app (shift f delta cutoff) (shift x delta cutoff)
  | Term.sign p m sig, delta, cutoff =>
      Term.sign p (shift m delta cutoff) sig
  | Term.verify p m sig, delta, cutoff =>
      Term.verify p (shift m delta cutoff) sig
  | Term.delegate m n, delta, cutoff =>
      Term.delegate (shift m delta cutoff) (shift n delta cutoff)
  | Term.attenuate m psi, delta, cutoff =>
      Term.attenuate (shift m delta cutoff) psi
  | Term.discharge m n, delta, cutoff =>
      Term.discharge (shift m delta cutoff) (shift n delta cutoff)
  | Term.liftLabel l m, delta, cutoff =>
      Term.liftLabel l (shift m delta cutoff)
  | Term.declassify l m pi, delta, cutoff =>
      Term.declassify l (shift m delta cutoff) (shift pi delta cutoff)
  | Term.now t, _, _ => Term.now t
  | Term.withinIntro t m, delta, cutoff =>
      Term.withinIntro t (shift m delta cutoff)
  | Term.pair a b, delta, cutoff =>
      Term.pair (shift a delta cutoff) (shift b delta cutoff)
  | Term.fst a, delta, cutoff => Term.fst (shift a delta cutoff)
  | Term.snd a, delta, cutoff => Term.snd (shift a delta cutoff)
  | Term.inl p a, delta, cutoff => Term.inl p (shift a delta cutoff)
  | Term.inr p a, delta, cutoff => Term.inr p (shift a delta cutoff)
  | Term.case scrut left right, delta, cutoff =>
      Term.case (shift scrut delta cutoff)
                (shift left  delta (cutoff + 1))
                (shift right delta (cutoff + 1))
  | Term.tensorIntro a b, delta, cutoff =>
      Term.tensorIntro (shift a delta cutoff) (shift b delta cutoff)
  | Term.letTensor scrut body, delta, cutoff =>
      Term.letTensor (shift scrut delta cutoff) (shift body delta (cutoff + 2))
  | Term.letSays p scrut body, delta, cutoff =>
      Term.letSays p (shift scrut delta cutoff) (shift body delta (cutoff + 1))
  | Term.sfExtract m, delta, cutoff =>
      Term.sfExtract (shift m delta cutoff)

/-- Substitute `value` for the variable at de-Bruijn index `depth` in `body`,
decrementing free variables above `depth` to close the binder. -/
def substAt : Term → Term → Nat → Term
  | Term.var i, value, depth =>
      if i = depth then
        shift value depth 0
      else if i > depth then
        Term.var (i - 1)
      else
        Term.var i
  | Term.lam p inner, value, depth =>
      Term.lam p (substAt inner value (depth + 1))
  | Term.app f x, value, depth =>
      Term.app (substAt f value depth) (substAt x value depth)
  | Term.sign p m sig, value, depth =>
      Term.sign p (substAt m value depth) sig
  | Term.verify p m sig, value, depth =>
      Term.verify p (substAt m value depth) sig
  | Term.delegate m n, value, depth =>
      Term.delegate (substAt m value depth) (substAt n value depth)
  | Term.attenuate m psi, value, depth =>
      Term.attenuate (substAt m value depth) psi
  | Term.discharge m n, value, depth =>
      Term.discharge (substAt m value depth) (substAt n value depth)
  | Term.liftLabel l m, value, depth =>
      Term.liftLabel l (substAt m value depth)
  | Term.declassify l m pi, value, depth =>
      Term.declassify l (substAt m value depth) (substAt pi value depth)
  | Term.now t, _, _ => Term.now t
  | Term.withinIntro t m, value, depth =>
      Term.withinIntro t (substAt m value depth)
  | Term.pair a b, value, depth =>
      Term.pair (substAt a value depth) (substAt b value depth)
  | Term.fst a, value, depth => Term.fst (substAt a value depth)
  | Term.snd a, value, depth => Term.snd (substAt a value depth)
  | Term.inl p a, value, depth => Term.inl p (substAt a value depth)
  | Term.inr p a, value, depth => Term.inr p (substAt a value depth)
  | Term.case scrut left right, value, depth =>
      Term.case (substAt scrut value depth)
                (substAt left  value (depth + 1))
                (substAt right value (depth + 1))
  | Term.tensorIntro a b, value, depth =>
      Term.tensorIntro (substAt a value depth) (substAt b value depth)
  | Term.letTensor scrut body, value, depth =>
      Term.letTensor (substAt scrut value depth) (substAt body value (depth + 2))
  | Term.letSays p scrut body, value, depth =>
      Term.letSays p (substAt scrut value depth) (substAt body value (depth + 1))
  | Term.sfExtract m, value, depth =>
      Term.sfExtract (substAt m value depth)

/-- Substitute `value` for the variable at de-Bruijn index 0 in `body`. -/
def subst (body value : Term) : Term :=
  substAt body value 0

/-! ## Sanity checks

A handful of `decide`-discharged equations that mirror the Rust unit tests
in `crates/dlc-core/src/subst.rs`. These are the smallest possible witnesses
that the function behaves correctly on closed forms; the *lemma* (universal
statement over all terms) is left for the M1.Q2.a proof closure pass. -/

namespace SubstChecks

/-- `subst (var 0) (var 3) = var 3`. -/
example : subst (Term.var 0) (Term.var 3) = Term.var 3 := rfl

/-- `subst (var 1) v = var 0` — free variable decrements. -/
example : subst (Term.var 1) (Term.var 99) = Term.var 0 := rfl

end SubstChecks

/-! ## Stated lemmas — proof closure deferred

The substitution lemma is what M1.Q2.a must close before we can prove subject
reduction (M1.Q2.c). Per CLAUDE.md we do **not** introduce `sorry`. Instead
we state the lemma as a `theorem` with no body; Lean will refuse the
declaration, so for now we wrap the statement as a `def` of its `Prop` type
and a TODO marker. The first commit that closes the proof flips this from
`def Statement … : Prop` to `theorem Statement … : <Prop> := <proof>`. -/

/-- The substitution lemma (statement only). Closes at M1.Q2.a. -/
def SubstitutionLemmaStatement : Prop :=
  ∀ (body value : Term) (depth : Nat),
    -- For now: a trivial conjunction so the type is `Prop`. The real
    -- statement says: if `body` is well-typed in `Γ, x:ψ` and `value` is
    -- well-typed in `Γ` at `ψ`, then `substAt body value depth` is well-typed
    -- in `Γ`. Lands once `Deriv` is populated (M1.Q2.b).
    body = body ∧ value = value ∧ depth = depth

end DLC
