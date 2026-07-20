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
  | Term.boxed o m n, delta, cutoff =>
      Term.boxed o (shift m delta cutoff) (shift n delta cutoff)
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
  | Term.saysBind p scrut body, delta, cutoff =>
      Term.saysBind p (shift scrut delta cutoff) (shift body delta (cutoff + 1))
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
  | Term.boxed o m n, value, depth =>
      Term.boxed o (substAt m value depth) (substAt n value depth)
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
  | Term.saysBind p scrut body, value, depth =>
      Term.saysBind p (substAt scrut value depth) (substAt body value (depth + 1))
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
  | boxed o m n ihM ihN => simp [shift, ihM, ihN]
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
  | saysBind p s b ihS ihB => simp [shift, ihS, ihB]
  | letSays p s b ihS ihB => simp [shift, ihS, ihB]
  | sfExtract m ih => simp [shift, ih]

/-! ## Substitution metatheory — status.

Two earlier definitions here (`SubstitutionCompositionStatement`,
`SubstitutionPreservesTypingStatement`, plus the alias
`SubstitutionLemmaStatement`) were tautological placeholders — their
bodies were `x = x` chains. They are deleted, not restated.

What is actually PROVEN lives in `DLC.Decidability`, for the
propositional fragment (`PropDeriv`):

* shift preservation — `propDeriv_shift` / `propDeriv_weaken_front`;
* substitution preservation — the public-facing lemma near
  `t1_propositional_soundness` (typing is preserved by `substAt` at
  arbitrary depth).

Also PROVEN, in this module (T3 rung 3a — the substitution composition
stack, below):

* the syntactic substitution-composition lemma over the full
  `Term` grammar (the Ramos et al., arXiv 2512.09280, shape) —
  `substAt_substAt`, together with its supporting lemmas
  `shift_shift_merge`, `shift_substAt_commute`, and
  `substAt_shift_cancel`.

What remains OPEN (tracked in the ledger):

* substitution preservation for the full `Deriv` judgment, which
  requires the linear-context splitting cases. -/

/-! ## Substitution composition stack (T3 rung 3a).

The four lemmas below are purely syntactic identities about `shift` and
`substAt` over the full `Term` grammar, proved by structural induction with
all indices generalized. `substAt_substAt` is the substitution composition
law; the other three are the shift/substitution commutation facts its
variable cases need. See `spec/t3-two-run-design-2026-07.md`. -/

/-- **Shift EXCHANGE.** Two shifts at nested cutoffs commute, with the outer
cutoff displaced by the inner delta. Distinct from `shift_shift_merge`, which
fuses same-direction nested shifts; this one SWAPS their order.

Needed by L3a: since the split rules now carry a `shift` in their conclusion
(the linear de Bruijn LEVEL migration), the shift lemma's `impE`-shaped cases
must reconcile `shift (shift N Γm Γl) Γ₁ (Γₐ + Γm)` -- what the constructor
produces -- with `shift (shift N Γ₁ Γₐ) Γm Γl`, what the goal carries. -/
theorem shift_shift_comm (d₁ d₂ : Nat) :
    ∀ (M : Term) (c₁ c₂ : Nat), c₁ ≤ c₂ →
      shift (shift M d₂ c₂) d₁ c₁ = shift (shift M d₁ c₁) d₂ (c₂ + d₁) := by
  intro M
  induction M with
  | var v =>
      intro c₁ c₂ h
      simp only [shift]
      split_ifs <;> simp only [shift] <;> split_ifs <;>
        first
          | rfl
          | exact congrArg Term.var (by omega)
          | omega
  | lam p b ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih (c₁ + 1) (c₂ + 1) (by omega),
          show c₂ + 1 + d₁ = c₂ + d₁ + 1 from by omega]
  | app f x ihf ihx =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihf c₁ c₂ h, ihx c₁ c₂ h]
  | sign p m sig ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | verify p m sig ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | delegate m n ihm ihn =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihm c₁ c₂ h, ihn c₁ c₂ h]
  | attenuate m ψ ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | boxed o m n ihm ihn =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihm c₁ c₂ h, ihn c₁ c₂ h]
  | discharge m n ihm ihn =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihm c₁ c₂ h, ihn c₁ c₂ h]
  | liftLabel l m ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | declassify l m π ihm ihπ =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihm c₁ c₂ h, ihπ c₁ c₂ h]
  | now t =>
      intro c₁ c₂ h
      simp only [shift]
  | withinIntro t m ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | pair a b iha ihb =>
      intro c₁ c₂ h
      simp only [shift]
      rw [iha c₁ c₂ h, ihb c₁ c₂ h]
  | fst a ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | snd a ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | inl p a ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | inr p a ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]
  | case s l r ihs ihl ihr =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihs c₁ c₂ h, ihl (c₁ + 1) (c₂ + 1) (by omega), ihr (c₁ + 1) (c₂ + 1) (by omega),
          show c₂ + 1 + d₁ = c₂ + d₁ + 1 from by omega]
  | tensorIntro a b iha ihb =>
      intro c₁ c₂ h
      simp only [shift]
      rw [iha c₁ c₂ h, ihb c₁ c₂ h]
  | letTensor s b ihs ihb =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihs c₁ c₂ h, ihb (c₁ + 2) (c₂ + 2) (by omega),
          show c₂ + 2 + d₁ = c₂ + d₁ + 2 from by omega]
  | saysBind p s b ihs ihb =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihs c₁ c₂ h, ihb (c₁ + 1) (c₂ + 1) (by omega),
          show c₂ + 1 + d₁ = c₂ + d₁ + 1 from by omega]
  | letSays p s b ihs ihb =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ihs c₁ c₂ h, ihb (c₁ + 1) (c₂ + 1) (by omega),
          show c₂ + 1 + d₁ = c₂ + d₁ + 1 from by omega]
  | sfExtract m ih =>
      intro c₁ c₂ h
      simp only [shift]
      rw [ih c₁ c₂ h]

/-- Merging two shifts when the outer cutoff lies within the inner shift's range. -/
theorem shift_shift_merge (d d' : Nat) :
    ∀ (M : Term) (c c' : Nat), c ≤ c' → c' ≤ c + d →
      shift (shift M d c) d' c' = shift M (d + d') c := by
  intro M
  induction M with
  | var v =>
      intro c c' h1 h2
      simp only [shift]
      by_cases hv : v < c
      · simp only [if_pos hv]
        simp only [shift]
        rw [if_pos (show v < c' by omega)]
      · simp only [if_neg hv]
        simp only [shift]
        rw [if_neg (show ¬ v + d < c' by omega)]
        exact congrArg Term.var (by omega)
  | lam p b ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih (c + 1) (c' + 1) (by omega) (by omega)]
  | app f x ihf ihx =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihf c c' h1 h2, ihx c c' h1 h2]
  | sign p m sig ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | verify p m sig ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | delegate m n ihm ihn =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihm c c' h1 h2, ihn c c' h1 h2]
  | attenuate m ψ ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | boxed o m n ihm ihn =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihm c c' h1 h2, ihn c c' h1 h2]
  | discharge m n ihm ihn =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihm c c' h1 h2, ihn c c' h1 h2]
  | liftLabel l m ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | declassify l m π ihm ihπ =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihm c c' h1 h2, ihπ c c' h1 h2]
  | now t =>
      intro c c' _ _
      simp only [shift]
  | withinIntro t m ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | pair a b iha ihb =>
      intro c c' h1 h2
      simp only [shift]
      rw [iha c c' h1 h2, ihb c c' h1 h2]
  | fst a ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | snd a ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | inl p a ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | inr p a ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]
  | case s l r ihs ihl ihr =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihs c c' h1 h2, ihl (c + 1) (c' + 1) (by omega) (by omega),
          ihr (c + 1) (c' + 1) (by omega) (by omega)]
  | tensorIntro a b iha ihb =>
      intro c c' h1 h2
      simp only [shift]
      rw [iha c c' h1 h2, ihb c c' h1 h2]
  | letTensor s b ihs ihb =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihs c c' h1 h2, ihb (c + 2) (c' + 2) (by omega) (by omega)]
  | saysBind p s b ihs ihb =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihs c c' h1 h2, ihb (c + 1) (c' + 1) (by omega) (by omega)]
  | letSays p s b ihs ihb =>
      intro c c' h1 h2
      simp only [shift]
      rw [ihs c c' h1 h2, ihb (c + 1) (c' + 1) (by omega) (by omega)]
  | sfExtract m ih =>
      intro c c' h1 h2
      simp only [shift]
      rw [ih c c' h1 h2]

/-- Shifting commutes with substitution when the cutoff is below the depth. -/
theorem shift_substAt_commute (d : Nat) (P : Term) :
    ∀ (M : Term) (i c : Nat), c ≤ i →
      shift (substAt M P i) d c = substAt (shift M d c) P (i + d) := by
  intro M
  induction M with
  | var v =>
      intro i c hci
      by_cases heq : v = i
      · rw [heq, substAt_var_eq P i,
            show shift (Term.var i) d c = Term.var (i + d) by
              simp only [shift]; rw [if_neg (by omega)],
            substAt_var_eq P (i + d)]
        exact shift_shift_merge i d P 0 c (Nat.zero_le _) (by omega)
      · by_cases hlt : v < i
        · rw [substAt_var_lt P v i hlt]
          simp only [shift]
          by_cases hvc : v < c
          · simp only [if_pos hvc]
            rw [substAt_var_lt P v (i + d) (by omega)]
          · simp only [if_neg hvc]
            rw [substAt_var_lt P (v + d) (i + d) (by omega)]
        · have hgt : i < v := by omega
          rw [substAt_var_gt P v i hgt]
          simp only [shift]
          rw [if_neg (show ¬ v - 1 < c by omega), if_neg (show ¬ v < c by omega),
              substAt_var_gt P (v + d) (i + d) (by omega)]
          exact congrArg Term.var (by omega)
  | lam p b ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [show i + d + 1 = i + 1 + d by omega, ih (i + 1) (c + 1) (by omega)]
  | app f x ihf ihx =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihf i c hci, ihx i c hci]
  | sign p m sig ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | verify p m sig ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | delegate m n ihm ihn =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihm i c hci, ihn i c hci]
  | attenuate m ψ ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | boxed o m n ihm ihn =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihm i c hci, ihn i c hci]
  | discharge m n ihm ihn =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihm i c hci, ihn i c hci]
  | liftLabel l m ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | declassify l m π ihm ihπ =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihm i c hci, ihπ i c hci]
  | now t =>
      intro i c _
      simp only [shift, substAt]
  | withinIntro t m ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | pair a b iha ihb =>
      intro i c hci
      simp only [shift, substAt]
      rw [iha i c hci, ihb i c hci]
  | fst a ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | snd a ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | inl p a ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | inr p a ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]
  | case s l r ihs ihl ihr =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihs i c hci, show i + d + 1 = i + 1 + d by omega,
          ihl (i + 1) (c + 1) (by omega), ihr (i + 1) (c + 1) (by omega)]
  | tensorIntro a b iha ihb =>
      intro i c hci
      simp only [shift, substAt]
      rw [iha i c hci, ihb i c hci]
  | letTensor s b ihs ihb =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihs i c hci, show i + d + 2 = i + 2 + d by omega,
          ihb (i + 2) (c + 2) (by omega)]
  | saysBind p s b ihs ihb =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihs i c hci, show i + d + 1 = i + 1 + d by omega,
          ihb (i + 1) (c + 1) (by omega)]
  | letSays p s b ihs ihb =>
      intro i c hci
      simp only [shift, substAt]
      rw [ihs i c hci, show i + d + 1 = i + 1 + d by omega,
          ihb (i + 1) (c + 1) (by omega)]
  | sfExtract m ih =>
      intro i c hci
      simp only [shift, substAt]
      rw [ih i c hci]

/-- Substituting at an index covered by a (d+1)-shift cancels one
shift. The substituted value `V` is arbitrary — it is never placed. -/
theorem substAt_shift_cancel (d : Nat) (V : Term) :
    ∀ (M : Term) (i c : Nat), c ≤ i → i ≤ c + d →
      substAt (shift M (d + 1) c) V i = shift M d c := by
  intro M
  induction M with
  | var v =>
      intro i c h1 h2
      simp only [shift]
      by_cases hvc : v < c
      · simp only [if_pos hvc]
        rw [substAt_var_lt V v i (by omega)]
      · simp only [if_neg hvc]
        rw [substAt_var_gt V (v + (d + 1)) i (by omega)]
        exact congrArg Term.var (by omega)
  | lam p b ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih (i + 1) (c + 1) (by omega) (by omega)]
  | app f x ihf ihx =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihf i c h1 h2, ihx i c h1 h2]
  | sign p m sig ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | verify p m sig ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | delegate m n ihm ihn =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihm i c h1 h2, ihn i c h1 h2]
  | attenuate m ψ ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | boxed o m n ihm ihn =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihm i c h1 h2, ihn i c h1 h2]
  | discharge m n ihm ihn =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihm i c h1 h2, ihn i c h1 h2]
  | liftLabel l m ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | declassify l m π ihm ihπ =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihm i c h1 h2, ihπ i c h1 h2]
  | now t =>
      intro i c _ _
      simp only [shift, substAt]
  | withinIntro t m ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | pair a b iha ihb =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [iha i c h1 h2, ihb i c h1 h2]
  | fst a ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | snd a ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | inl p a ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | inr p a ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]
  | case s l r ihs ihl ihr =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihs i c h1 h2, ihl (i + 1) (c + 1) (by omega) (by omega),
          ihr (i + 1) (c + 1) (by omega) (by omega)]
  | tensorIntro a b iha ihb =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [iha i c h1 h2, ihb i c h1 h2]
  | letTensor s b ihs ihb =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihs i c h1 h2, ihb (i + 2) (c + 2) (by omega) (by omega)]
  | saysBind p s b ihs ihb =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihs i c h1 h2, ihb (i + 1) (c + 1) (by omega) (by omega)]
  | letSays p s b ihs ihb =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ihs i c h1 h2, ihb (i + 1) (c + 1) (by omega) (by omega)]
  | sfExtract m ih =>
      intro i c h1 h2
      simp only [shift, substAt]
      rw [ih i c h1 h2]

/-- THE substitution composition law (j ≤ k). -/
theorem substAt_substAt (N P : Term) :
    ∀ (M : Term) (j k : Nat), j ≤ k →
      substAt (substAt M N j) P k
        = substAt (substAt M P (k + 1)) (substAt N P (k - j)) j := by
  intro M
  induction M with
  | var v =>
      intro j k hjk
      by_cases hvj : v = j
      · rw [hvj, substAt_var_eq N j, substAt_var_lt P j (k + 1) (by omega),
            substAt_var_eq (substAt N P (k - j)) j]
        have h := shift_substAt_commute j P N (k - j) 0 (Nat.zero_le _)
        rw [show k - j + j = k by omega] at h
        exact h.symm
      · by_cases hvk : v = k + 1
        · rw [hvk, substAt_var_gt N (k + 1) j (by omega),
              show k + 1 - 1 = k by omega, substAt_var_eq P k,
              substAt_var_eq P (k + 1)]
          exact (substAt_shift_cancel k (substAt N P (k - j)) P j 0
            (Nat.zero_le _) (by omega)).symm
        · by_cases hlt : v < j
          · rw [substAt_var_lt N v j hlt, substAt_var_lt P v k (by omega),
                substAt_var_lt P v (k + 1) (by omega),
                substAt_var_lt (substAt N P (k - j)) v j hlt]
          · have hgt : j < v := by omega
            by_cases hle : v ≤ k
            · rw [substAt_var_gt N v j hgt,
                  substAt_var_lt P (v - 1) k (by omega),
                  substAt_var_lt P v (k + 1) (by omega),
                  substAt_var_gt (substAt N P (k - j)) v j hgt]
            · rw [substAt_var_gt N v j hgt,
                  substAt_var_gt P (v - 1) k (by omega),
                  substAt_var_gt P v (k + 1) (by omega),
                  substAt_var_gt (substAt N P (k - j)) (v - 1) j (by omega)]
  | lam p b ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih (j + 1) (k + 1) (by omega),
          show k + 1 - (j + 1) = k - j by omega]
  | app f x ihf ihx =>
      intro j k hjk
      simp only [substAt]
      rw [ihf j k hjk, ihx j k hjk]
  | sign p m sig ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | verify p m sig ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | delegate m n ihm ihn =>
      intro j k hjk
      simp only [substAt]
      rw [ihm j k hjk, ihn j k hjk]
  | attenuate m ψ ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | boxed o m n ihm ihn =>
      intro j k hjk
      simp only [substAt]
      rw [ihm j k hjk, ihn j k hjk]
  | discharge m n ihm ihn =>
      intro j k hjk
      simp only [substAt]
      rw [ihm j k hjk, ihn j k hjk]
  | liftLabel l m ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | declassify l m π ihm ihπ =>
      intro j k hjk
      simp only [substAt]
      rw [ihm j k hjk, ihπ j k hjk]
  | now t =>
      intro j k _
      simp only [substAt]
  | withinIntro t m ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | pair a b iha ihb =>
      intro j k hjk
      simp only [substAt]
      rw [iha j k hjk, ihb j k hjk]
  | fst a ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | snd a ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | inl p a ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | inr p a ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]
  | case s l r ihs ihl ihr =>
      intro j k hjk
      simp only [substAt]
      rw [ihs j k hjk, ihl (j + 1) (k + 1) (by omega),
          ihr (j + 1) (k + 1) (by omega),
          show k + 1 - (j + 1) = k - j by omega]
  | tensorIntro a b iha ihb =>
      intro j k hjk
      simp only [substAt]
      rw [iha j k hjk, ihb j k hjk]
  | letTensor s b ihs ihb =>
      intro j k hjk
      simp only [substAt]
      rw [ihs j k hjk, ihb (j + 2) (k + 2) (by omega),
          show k + 2 + 1 = k + 1 + 2 by omega,
          show k + 2 - (j + 2) = k - j by omega]
  | saysBind p s b ihs ihb =>
      intro j k hjk
      simp only [substAt]
      rw [ihs j k hjk, ihb (j + 1) (k + 1) (by omega),
          show k + 1 - (j + 1) = k - j by omega]
  | letSays p s b ihs ihb =>
      intro j k hjk
      simp only [substAt]
      rw [ihs j k hjk, ihb (j + 1) (k + 1) (by omega),
          show k + 1 - (j + 1) = k - j by omega]
  | sfExtract m ih =>
      intro j k hjk
      simp only [substAt]
      rw [ih j k hjk]

end DLC
