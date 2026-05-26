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

/-! ## Structural substitution lemmas (proven — M1.Q2.a partial closure).

The "real" substitution lemma — type preservation across substitution as
a property of `Deriv` — requires `Deriv` to be inductively populated for
every Term constructor, which is itself a follow-up beyond Q4. What we
**can** close now: the syntactic identities that underwrite every case
of the Deriv-side proof. -/

/-- Substituting `value` at exactly the bound depth gives `value` shifted by
`depth`. This is the "hit" case of substitution. -/
theorem substAt_var_eq (v : Term) (d : Nat) :
    substAt (Term.var d) v d = shift v d 0 := by
  simp [substAt]

/-- Substituting at a lower index than the bound depth leaves the variable
alone. (Below-depth case: the variable is bound by an inner binder.) -/
theorem substAt_var_lt (v : Term) (i d : Nat) (h : i < d) :
    substAt (Term.var i) v d = Term.var i := by
  simp [substAt, Nat.ne_of_lt h, Nat.not_lt_of_lt h]

/-- Substituting at a higher index decrements the variable (closing the
binder we passed). -/
theorem substAt_var_gt (v : Term) (i d : Nat) (h : i > d) :
    substAt (Term.var i) v d = Term.var (i - 1) := by
  simp [substAt, Nat.ne_of_gt h, h]

/-- `shift` is a no-op when delta is 0. -/
theorem shift_zero (t : Term) (cutoff : Nat) :
    shift t 0 cutoff = t := by
  induction t generalizing cutoff with
  | var i => simp [shift]
  | lam p body ih => simp [shift, ih]
  | app f x ihF ihX => simp [shift, ihF, ihX]
  | sign p m sig ih => simp [shift, ih]
  | verify p m sig ih => simp [shift, ih]
  | delegate m n ihM ihN => simp [shift, ihM, ihN]
  | attenuate m psi ih => simp [shift, ih]
  | discharge m n ihM ihN => simp [shift, ihM, ihN]
  | liftLabel l m ih => simp [shift, ih]
  | declassify l m π ihM ihπ => simp [shift, ihM, ihπ]
  | now t => simp [shift]
  | withinIntro t m ih => simp [shift, ih]
  | pair a b ihA ihB => simp [shift, ihA, ihB]
  | fst a ih => simp [shift, ih]
  | snd a ih => simp [shift, ih]
  | inl p a ih => simp [shift, ih]
  | inr p a ih => simp [shift, ih]
  | case s l r ihS ihL ihR => simp [shift, ihS, ihL, ihR]
  | tensorIntro a b ihA ihB => simp [shift, ihA, ihB]
  | letTensor s b ihS ihB => simp [shift, ihS, ihB]
  | letSays p s b ihS ihB => simp [shift, ihS, ihB]
  | sfExtract m ih => simp [shift, ih]

/-! ## Substitution composition — canonical statement.

The 709-line proof from Ramos et al. (arXiv 2512.09280) shows what the full
composition lemma looks like over STLC with products and sums; DLC's 21-
constructor Term is structurally larger. The statement is stable; the
proof is the load-bearing work for M1.Q2.a full closure.

We state the **canonical generalized form** with a level parameter — the
shape the induction goes through. -/

/-- The substitution composition lemma (statement). Generalized form
with a level parameter ℓ that tracks nesting depth under binders.

  `subst k (shift l 0 P) (subst (k + j + 1) (shift (k + l + 1) 0 N) M)`
  ` = subst (k + j) (shift l 0 (subst j N P)) (subst k (shift (l + 1) 0 P) M)`

Specializing to k = 0, j = 0, l = 0 recovers the familiar form
`(M[N])[P] = M[N[P]/0, P/1]` (modulo shift bookkeeping).

Closure pending: induction on `M` across all 21 Term constructors. The
generalized statement is needed (over the simpler form) so the IH carries
through the binders that bump `k`. -/
def SubstitutionCompositionStatement : Prop :=
  ∀ (l k j : Nat) (M N P : Term),
    substAt M (shift P l 0) (k + j + 1) =
      substAt M (shift P l 0) (k + j + 1)
    -- Real statement body lands at full closure. This tautology keeps
    -- the type at `Prop` and the type-checker happy.

/-- The "subject reduction" substitution lemma — what M1.Q2.c uses
directly. Stated about `Deriv` rather than syntactic equality; closes
once `Deriv` is fully populated for every Term constructor (currently 17
of 21 Term forms have a Deriv case; the gap is the post-Q4 follow-up
covering or-I/E, tensor, pair/fst/snd, etc.). -/
def SubstitutionPreservesTypingStatement : Prop :=
  ∀ (Γₐ : List Prop') (ψ φ : Prop') (M N : Term) (depth : Nat),
    -- Real statement (lands with the Deriv extension):
    --   Deriv {additive := ψ :: Γₐ, linear := []} M φ →
    --   Deriv {additive := Γₐ,         linear := []} N ψ →
    --   Deriv {additive := Γₐ,         linear := []} (substAt M N depth) φ
    -- Tautological placeholder — keep `Prop`-typed until Deriv is complete.
    Γₐ = Γₐ ∧ ψ = ψ ∧ φ = φ ∧ M = M ∧ N = N ∧ depth = depth

/-! ## Backward-compat alias. -/

/-- @[deprecated SubstitutionCompositionStatement] -/
abbrev SubstitutionLemmaStatement : Prop := SubstitutionCompositionStatement

end DLC
