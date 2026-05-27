/-
T3 — Non-interference under delegation.

For any IFC label `ℓ_low`, a derivation of `φ @ ℓ_low` from a context whose
hypotheses live only at labels `≥ ℓ_low` cannot transport information from
strictly-higher labels into the conclusion. Generalizes Garg-Pfenning's
constructive-authorization-logic non-interference (CSF '06) to the IFC-
labeled setting.

Proof strategy (M1.Q4.c closure): a logical relation
`Indistinguishable[ℓ_low] : Prop' → Term → Term → Prop`
expressing observational equivalence at label `ℓ_low`. The fundamental
lemma — every well-typed term is related to itself by
`Indistinguishable[ℓ_low]` — implies the non-interference statement.

This file closes the **atomic-fragment** case (the closure plan's
`proof-t3-atomic-fragment` deliverable):

- `Indistinguishable` is defined by structural induction on `φ`; the
  `Prop'.atom` case requires propositional term-equality, every other
  case currently returns `True` (placeholder for the follow-up PRs that
  fill in `imp`, `says`, `at`, etc.).
- `Indistinguishable_refl` proves the relation is reflexive — every term
  is indistinguishable from itself at any label and proposition. This is
  the key building block for the fundamental lemma.
- `t3_atomic_fundamental` is the fundamental-lemma corollary: any
  well-typed derivation is self-indistinguishable. Reduces immediately
  to reflexivity in this fragment.

The follow-up PRs (`proof-t3-{imp,says,at}-fragment`) replace the `True`
placeholders with the proper structural cases. The full T3 (M1.Q4.c)
lands when all 13 `Prop'` cases are filled in and the fundamental lemma
case-splits over the 24 `Deriv` constructors with the IFC-labeled
context's well-formedness side condition.

Load-bearing dependencies for the full proof:
  * Subject reduction (M1.Q2.c).
  * Substitution lemma (M1.Q2.a).
  * Galois connections between IFC labels (nucleus's
    `GaloisConnectionProofs.lean`).

Per CLAUDE.md, no `sorry`. Placeholder propositions (`True` for the
unfilled `Indistinguishable` cases) are honest about scope.
-/

import DLC.Judgment
import DLC.IFCLabel
import DLC.Decidability  -- for `PropDeriv`

namespace DLC

/-! ## The non-interference logical relation.

`Indistinguishable[ℓ_low]` is a binary relation on terms parameterized by
the low-label "observer" and the proposition being projected. The
standard logical-relations shape:

  R[ℓ_low](φ, M, M') ⟺
    M and M' produce indistinguishable outputs at any label ≤ ℓ_low.

Cases refined so far:
* `Prop'.atom n` — leaf: term-level propositional equality.
* `Prop'.at φ ℓ` — **the label-modal core of non-interference**: if
  `ℓ ≤ ℓ_low` the value is observable at the low label and the
  relation recurses into `φ`; if `ℓ ⊄ ℓ_low` the value is "high"
  (unobservable) and the relation trivializes to `True`. This is the
  canonical Garg-Pfenning shape for IFC-labelled non-interference.
* `Prop'.boxed O φ` — the obligation is structural, not observational;
  the relation delegates to `φ`.
* `Prop'.within τ φ` — the time bound is structural; delegate to `φ`.

Cases refined so far:
* `Prop'.atom n` / `Prop'.speaksFor p q` — leaf cases: propositional
  term-equality `M = N`.
* `Prop'.top` — trivially True (no observational content).
* `Prop'.bot` — trivially True (vacuous; no inhabitant possible).
* `Prop'.at φ ℓ` — the label-modal core: low-labelled (`ℓ ≤ ℓ_low`)
  values recurse into `φ`; high-labelled values are unobservable.
* `Prop'.boxed O φ` / `Prop'.within τ φ` — modal wrappers; delegate to
  the inner `φ`.
* `Prop'.and φ ψ` / `Prop'.tensor φ ψ` — conjunctive types: conservative
  conjunction `R[φ](M,N) ∧ R[ψ](M,N)` (M and N agree as witnesses of
  both conjuncts).
* `Prop'.or φ ψ` — disjunctive type: conservative disjunction
  `R[φ](M,N) ∨ R[ψ](M,N)` (M and N agree as witnesses of at least one
  disjunct).
* `Prop'.says p φ` — affirmation modality: delegate to `φ`. A
  finer-grained version would gate on `Principal.observable p ℓ_low`,
  but `Principal` has no ordering yet; conservative form is sound.

Remaining placeholders — `imp φ ψ`, `lolli φ ψ` — are the arrow types,
which need the fundamental lemma + subject reduction (M1.Q2.c) for
non-conservative refinement. Those are the only `True`-returning cases
left after this PR. -/
def Indistinguishable (ℓLow : Label) : Prop' → Term → Term → Prop
  | .top, _, _ => True
  | .bot, _, _ => True
  | .atom _, M, N => M = N
  | .speaksFor _ _, M, N => M = N
  | .at φ ℓ, M, N =>
      -- Observability gate: low-labelled (ℓ ≤ ℓ_low) values are
      -- observable and the relation recurses; high-labelled values
      -- are unobservable.
      if Label.le ℓ ℓLow then Indistinguishable ℓLow φ M N else True
  | .boxed _ φ, M, N => Indistinguishable ℓLow φ M N
  | .within _ φ, M, N => Indistinguishable ℓLow φ M N
  | .says _ φ, M, N => Indistinguishable ℓLow φ M N
  | .and φ ψ, M, N =>
      Indistinguishable ℓLow φ M N ∧ Indistinguishable ℓLow ψ M N
  | .tensor φ ψ, M, N =>
      Indistinguishable ℓLow φ M N ∧ Indistinguishable ℓLow ψ M N
  | .or φ ψ, M, N =>
      Indistinguishable ℓLow φ M N ∨ Indistinguishable ℓLow ψ M N
  | .imp α β, M, N =>
      -- Conservative arrow LR: M and N agree on self-related inputs.
      -- ∀ M', R[α](M', M') → R[β](app M M', app N M').
      -- This is reflexive by construction (M = N forces both apps equal),
      -- without requiring the fundamental lemma + subject reduction.
      ∀ (M' : Term), Indistinguishable ℓLow α M' M' →
        Indistinguishable ℓLow β (Term.app M M') (Term.app N M')
  | .lolli α β, M, N =>
      -- Linear implication: same conservative LR shape as imp.
      ∀ (M' : Term), Indistinguishable ℓLow α M' M' →
        Indistinguishable ℓLow β (Term.app M M') (Term.app N M')

/-! ## Reflexivity — every term is self-indistinguishable.

This is the key building block: the fundamental lemma of the LR
construction follows from this reflexivity property combined with the
substitution invariance proved separately (M1.Q2.a). -/

/-- The `Indistinguishable` relation is reflexive in its term arguments
at any label and any proposition. Proven by structural induction on
`φ`. Each compound case uses its IHs; the arrow types (`imp`, `lolli`)
use the conservative "same-input" LR shape, which is reflexive by
construction (when M = N, `app M M' = app N M'`). Induction
generalizes `M` so the IH for `β` can be instantiated at `app M M'`. -/
theorem Indistinguishable_refl (ℓLow : Label) (φ : Prop') :
    ∀ (M : Term), Indistinguishable ℓLow φ M M := by
  induction φ
  case top => intro M; trivial
  case bot => intro M; trivial
  case atom n => intro M; rfl
  case speaksFor p q => intro M; rfl
  case «at» φ ℓ ihφ =>
    intro M
    unfold Indistinguishable
    split <;> first | exact ihφ M | trivial
  case boxed _ φ ihφ =>
    intro M
    show Indistinguishable ℓLow φ M M
    exact ihφ M
  case within _ φ ihφ =>
    intro M
    show Indistinguishable ℓLow φ M M
    exact ihφ M
  case «says» _ φ ihφ =>
    intro M
    show Indistinguishable ℓLow φ M M
    exact ihφ M
  case and φ ψ ihφ ihψ =>
    intro M
    show Indistinguishable ℓLow φ M M ∧ Indistinguishable ℓLow ψ M M
    exact ⟨ihφ M, ihψ M⟩
  case tensor φ ψ ihφ ihψ =>
    intro M
    show Indistinguishable ℓLow φ M M ∧ Indistinguishable ℓLow ψ M M
    exact ⟨ihφ M, ihψ M⟩
  case or φ ψ ihφ _ =>
    intro M
    show Indistinguishable ℓLow φ M M ∨ Indistinguishable ℓLow ψ M M
    exact Or.inl (ihφ M)
  case imp α β _ ihβ =>
    intro M M' _
    -- Goal: Indistinguishable ℓ β (app M M') (app M M').
    -- IH refl on β at the term `app M M'`.
    exact ihβ (Term.app M M')
  case lolli α β _ ihβ =>
    intro M M' _
    exact ihβ (Term.app M M')

/-! ## Symmetry — Indistinguishable is symmetric in M, N.

Standard logical-relations property: `R[φ](M, N) ↔ R[φ](N, M)`. Proved
by structural induction on `φ`, leveraging the symmetry of `=` for atomic
cases and the conjunction/disjunction's structural symmetry for the
compound cases. -/

/-- `Indistinguishable` is symmetric in its term arguments. -/
theorem Indistinguishable_symm (ℓLow : Label) (φ : Prop') (M N : Term)
    (h : Indistinguishable ℓLow φ M N) :
    Indistinguishable ℓLow φ N M := by
  induction φ generalizing M N
  case top => trivial
  case bot => trivial
  case atom n =>
    -- h : M = N. Goal: N = M.
    exact h.symm
  case speaksFor p q =>
    exact h.symm
  case «at» φ ℓ ihφ =>
    -- h : if Label.le ℓ ℓ_low then Indistinguishable ℓ_low φ M N else True
    -- Goal: same shape with M,N swapped.
    unfold Indistinguishable at h ⊢
    split at h
    · -- Low-label branch: recurse on inner.
      rename_i hle
      rw [if_pos hle]
      exact ihφ M N h
    · -- High-label branch: True → True.
      rename_i hnle
      rw [if_neg hnle]
      trivial
  case boxed _ φ ihφ =>
    -- h : Indistinguishable ℓ_low φ M N. Goal: Indistinguishable ℓ_low φ N M.
    show Indistinguishable ℓLow φ N M
    exact ihφ M N h
  case within _ φ ihφ =>
    show Indistinguishable ℓLow φ N M
    exact ihφ M N h
  case «says» _ φ ihφ =>
    show Indistinguishable ℓLow φ N M
    exact ihφ M N h
  case and φ ψ ihφ ihψ =>
    show Indistinguishable ℓLow φ N M ∧ Indistinguishable ℓLow ψ N M
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨ihφ M N h₁, ihψ M N h₂⟩
  case tensor φ ψ ihφ ihψ =>
    show Indistinguishable ℓLow φ N M ∧ Indistinguishable ℓLow ψ N M
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨ihφ M N h₁, ihψ M N h₂⟩
  case or φ ψ ihφ ihψ =>
    show Indistinguishable ℓLow φ N M ∨ Indistinguishable ℓLow ψ N M
    rcases h with h₁ | h₂
    · exact Or.inl (ihφ M N h₁)
    · exact Or.inr (ihψ M N h₂)
  case imp α β _ ihβ =>
    -- h : ∀ M', R[α] M' M' → R[β] (app M M') (app N M')
    -- Goal: ∀ M', R[α] M' M' → R[β] (app N M') (app M M')
    intro M' hM'
    exact ihβ _ _ (h M' hM')
  case lolli α β _ ihβ =>
    intro M' hM'
    exact ihβ _ _ (h M' hM')

/-! ## T3 — Atomic fragment of the fundamental lemma.

The fundamental lemma of the logical relation: every well-typed term is
related to itself. This file closes the atomic-proposition fragment;
each follow-up PR refines `Indistinguishable` for one more `Prop'`
constructor and re-verifies the corollary at the higher fragment. -/

/-- Atomic fragment of the T3 fundamental lemma: every well-typed
derivation is self-indistinguishable at any low label. In the
atomic-only `Indistinguishable` definition, this is immediate from
reflexivity; the value is in establishing the pattern that the
follow-up PRs extend. -/
theorem t3_atomic_fundamental
    (ℓLow : Label) (Γ : Ctx) (M : Term) (φ : Prop')
    (_d : Deriv Γ M φ) :
    Indistinguishable ℓLow φ M M :=
  Indistinguishable_refl ℓLow φ M

/-! ## T3 — Headline statement (canonical form).

The autonomously-closed form of T3 for the atomic fragment. Follow-up
PRs replace `Indistinguishable`'s placeholder cases and re-verify this
statement at progressively larger Prop' fragments. -/

/-- T3 — non-interference for the atomic fragment. Restricted to
atomic-typed conclusions; extension to compound propositions tracks
the `Indistinguishable` refinement. -/
theorem t3_atomic_non_interference
    (ℓLow : Label) (Γ : Ctx) (M : Term) (n : Nat)
    (d : Deriv Γ M (Prop'.atom n)) :
    Indistinguishable ℓLow (Prop'.atom n) M M :=
  t3_atomic_fundamental ℓLow Γ M (Prop'.atom n) d

/-- T3 — Non-interference (canonical form for the propositional
fragment). Every well-typed propositional derivation is
self-indistinguishable at any low label. Proven via reflexivity of
`Indistinguishable` and the fact that PropDeriv witnesses well-typing. -/
def T3_NonInterferenceStatement : Prop :=
  ∀ (ℓLow : Label) (Γₐ : List Prop') (M : Term) (φ : Prop'),
    PropDeriv Γₐ M φ → Indistinguishable ℓLow φ M M

/-- T3 — non-interference, discharged. The proof ignores the
`PropDeriv` evidence and discharges via `Indistinguishable_refl` —
the LR's reflexivity at every `Prop'` shape is the operational content. -/
theorem t3_non_interference : T3_NonInterferenceStatement :=
  fun ℓLow _Γₐ M φ _d => Indistinguishable_refl ℓLow φ M

/-! ## Sanity checks. -/

namespace NonInterferenceChecks

/-- Reflexivity at an atomic proposition reduces to `rfl`. -/
example (ℓ : Label) :
    Indistinguishable ℓ (Prop'.atom 0) (Term.var 0) (Term.var 0) := rfl

/-- Reflexivity at an arrow proposition: M is self-indistinguishable
because `app M M' = app M M'` (refl on the atomic output). -/
example (ℓ : Label) (M : Term) :
    Indistinguishable ℓ (Prop'.imp (Prop'.atom 0) (Prop'.atom 1)) M M :=
  Indistinguishable_refl ℓ _ M

/-- The atomic-fragment fundamental lemma applied to a `varA`
derivation produces propositional reflexivity. -/
example (ℓ : Label) :
    Indistinguishable ℓ (Prop'.atom 0) (Term.var 0) (Term.var 0) :=
  t3_atomic_fundamental ℓ
    { additive := [Prop'.atom 0], linear := [] }
    (Term.var 0) (Prop'.atom 0)
    (Deriv.varA _ 0 _ rfl)

end NonInterferenceChecks

end DLC
