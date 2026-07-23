/-
T3 — Non-interference under delegation.

## Status: NOT PROVEN in any fragment (2026-07 audit).

Everything currently proven in this file is reflexivity, symmetry, and
transitivity of the `Indistinguishable` relation — one-run facts that
discard the typing derivation and hold for ill-typed terms. No two-run
statement (two derivations differing in high-labeled hypotheses) exists
anywhere in this development, and no lemma here is proven by induction
on a derivation. See the "T3 status" section note before
`t3_atomic_fundamental`. The ledger reports T3 as `stated`.

The intended theorem: for any IFC label `ℓ_low`, a derivation of
`φ @ ℓ_low` from a context whose hypotheses live only at labels
`≥ ℓ_low` cannot transport information from strictly-higher labels
into the conclusion. Would generalize Garg-Pfenning's constructive-
authorization-logic non-interference (CSF '06) to the IFC-labeled
setting.

Proof strategy (M1.Q4.c closure): a logical relation
`Indistinguishable[ℓ_low] : Prop' → Term → Term → Prop`
expressing observational equivalence at label `ℓ_low`. The fundamental
lemma — every well-typed term is related to itself by
`Indistinguishable[ℓ_low]` — implies the non-interference statement.

What this file currently contains:

- `Indistinguishable`, defined by structural induction on `φ`. Every
  case has structural content, but two shapes make it UNSUITABLE for a
  two-run fundamental lemma (see `spec/t3-two-run-design-2026-07.md`
  §"why"): the product cases apply both component types to the WHOLE
  term (non-projective), and the arrow cases are the conservative
  diagonal form (`∀ M', R M' M' → …`), chosen so reflexivity closes
  without reduction machinery.
- `Indistinguishable_refl` / `_symm` / `_trans` — one-run facts about
  the relation itself. Reflexivity is what the misleadingly-named
  theorems below discharge; it is NOT a fundamental lemma (nothing
  here inducts on a derivation).

The first REAL two-run statement lives in
`DLC.NonInterferenceTwoRun` (intro-fragment confinement, syntactic
strength, typing load-bearing — with witness `DLC.Witness.T3`); the
full theorem's rung ladder is in the design doc.

Load-bearing dependencies for the real proof:
  * Subject reduction (M1.Q2.c).
  * Substitution lemma (M1.Q2.a).
  * Galois connections between IFC labels (nucleus's
    `GaloisConnectionProofs.lean`).

Per CLAUDE.md, no `sorry`. Placeholder propositions (`True` for the
unfilled `Indistinguishable` cases) are declared in place.
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
      -- Refined to conjunction (was disjunction): low-observer can
      -- probe both disjuncts independently, so indistinguishability at
      -- `or` requires indistinguishability at *both* sides. This
      -- preserves reflexivity (by IH on each side) and is required for
      -- transitivity (mixed Or.inl/Or.inr cases were structurally
      -- non-composable under disjunction).
      Indistinguishable ℓLow φ M N ∧ Indistinguishable ℓLow ψ M N
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
  | .replicated φ, M, N =>
      -- COLLAPSING definition (design §5.2): a replicated value is
      -- low-related iff its underlying `φ`-value is — convergence collapses
      -- replicas to one observable. This delegates to `φ` exactly as the
      -- `boxed`/`within`/`says` modalities do, so reflexivity / symmetry /
      -- transitivity re-found by the single IH. (Inert this increment:
      -- `replicated` is untypable, so it never actually arises.)
      Indistinguishable ℓLow φ M N

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
  case or φ ψ ihφ ihψ =>
    intro M
    show Indistinguishable ℓLow φ M M ∧ Indistinguishable ℓLow ψ M M
    exact ⟨ihφ M, ihψ M⟩
  case imp α β _ ihβ =>
    intro M M' _
    -- Goal: Indistinguishable ℓ β (app M M') (app M M').
    -- IH refl on β at the term `app M M'`.
    exact ihβ (Term.app M M')
  case lolli α β _ ihβ =>
    intro M M' _
    exact ihβ (Term.app M M')
  case replicated φ ihφ =>
    intro M
    show Indistinguishable ℓLow φ M M
    exact ihφ M

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
    show Indistinguishable ℓLow φ N M ∧ Indistinguishable ℓLow ψ N M
    exact ⟨ihφ M N h.1, ihψ M N h.2⟩
  case imp α β _ ihβ =>
    -- h : ∀ M', R[α] M' M' → R[β] (app M M') (app N M')
    -- Goal: ∀ M', R[α] M' M' → R[β] (app N M') (app M M')
    intro M' hM'
    exact ihβ _ _ (h M' hM')
  case lolli α β _ ihβ =>
    intro M' hM'
    exact ihβ _ _ (h M' hM')
  case replicated φ ihφ =>
    show Indistinguishable ℓLow φ N M
    exact ihφ M N h

/-! ## Transitivity — Indistinguishable is transitive in M, N, P.

Standard PER property `R[φ](M, N) ∧ R[φ](N, P) → R[φ](M, P)`. Proven
by structural induction on `φ`. The or-case is closed by the
conjunctive refinement: both components compose via their IHs.
The arrow cases (imp/lolli) use the IH on the codomain at the
applied terms — the conservative same-input arrow LR makes the
input-equality assumption shared. -/

/-- `Indistinguishable` is transitive in its term arguments. -/
theorem Indistinguishable_trans (ℓLow : Label) (φ : Prop')
    (M N P : Term)
    (h12 : Indistinguishable ℓLow φ M N)
    (h23 : Indistinguishable ℓLow φ N P) :
    Indistinguishable ℓLow φ M P := by
  induction φ generalizing M N P
  case top => trivial
  case bot => trivial
  case atom n =>
    -- h12 : M = N; h23 : N = P. Goal: M = P.
    exact h12.trans h23
  case speaksFor p q =>
    exact h12.trans h23
  case «at» φ ℓ ihφ =>
    unfold Indistinguishable at h12 h23 ⊢
    split at h12
    · rename_i hle
      rw [if_pos hle] at h23
      rw [if_pos hle]
      exact ihφ M N P h12 h23
    · rename_i hnle
      rw [if_neg hnle]
      trivial
  case boxed _ φ ihφ =>
    show Indistinguishable ℓLow φ M P
    exact ihφ M N P h12 h23
  case within _ φ ihφ =>
    show Indistinguishable ℓLow φ M P
    exact ihφ M N P h12 h23
  case «says» _ φ ihφ =>
    show Indistinguishable ℓLow φ M P
    exact ihφ M N P h12 h23
  case and φ ψ ihφ ihψ =>
    show Indistinguishable ℓLow φ M P ∧ Indistinguishable ℓLow ψ M P
    exact ⟨ihφ M N P h12.1 h23.1, ihψ M N P h12.2 h23.2⟩
  case tensor φ ψ ihφ ihψ =>
    show Indistinguishable ℓLow φ M P ∧ Indistinguishable ℓLow ψ M P
    exact ⟨ihφ M N P h12.1 h23.1, ihψ M N P h12.2 h23.2⟩
  case or φ ψ ihφ ihψ =>
    -- With the conjunctive refinement, both components compose.
    show Indistinguishable ℓLow φ M P ∧ Indistinguishable ℓLow ψ M P
    exact ⟨ihφ M N P h12.1 h23.1, ihψ M N P h12.2 h23.2⟩
  case imp α β _ ihβ =>
    -- h12 : ∀ M', R[α] M' M' → R[β] (app M M') (app N M')
    -- h23 : ∀ M', R[α] M' M' → R[β] (app N M') (app P M')
    -- Goal: ∀ M', R[α] M' M' → R[β] (app M M') (app P M')
    intro M' hM'
    exact ihβ _ _ _ (h12 M' hM') (h23 M' hM')
  case lolli α β _ ihβ =>
    intro M' hM'
    exact ihβ _ _ _ (h12 M' hM') (h23 M' hM')
  case replicated φ ihφ =>
    show Indistinguishable ℓLow φ M P
    exact ihφ M N P h12 h23

/-! ## T3 status — the theorems below are NOT non-interference.

Honest accounting (2026-07 audit): everything in this section is
proven by REFLEXIVITY of `Indistinguishable`, with the typing
derivation passed in and discarded (note the `_d` binders). The
statements are true, but they carry no information-flow content:

* they relate every term to ITSELF, not two runs of a program that
  differ in high-labeled inputs;
* they hold for ill-typed terms just as well — the derivation
  hypothesis does no work;
* no fundamental lemma exists: nothing here is proven by induction
  on the derivation.

Real (two-run) non-interference — a logical relation over pairs of
derivations differing in hypotheses above `ℓLow`, with a fundamental
lemma in the Garg-Pfenning / FLAFOL style — is OPEN, tracked in the
ledger as T3's actual content, and is Phase-2 scope. The lemmas below
are retained only as the reflexivity/symmetry/transitivity
infrastructure of the relation that proof will need. -/

/-- Reflexivity of the LR at every `Prop'` shape, wrapped with a
(discarded) typing hypothesis. NOT a fundamental lemma: the derivation
does no work — see the section note. -/
theorem t3_atomic_fundamental
    (ℓLow : Label) (Γ : Ctx) (M : Term) (φ : Prop')
    (_d : Deriv Γ M φ) :
    Indistinguishable ℓLow φ M M :=
  Indistinguishable_refl ℓLow φ M

/-- Reflexivity at atomic conclusions. Same caveat as
`t3_atomic_fundamental`: no information-flow content. -/
theorem t3_atomic_non_interference
    (ℓLow : Label) (Γ : Ctx) (M : Term) (n : Nat)
    (d : Deriv Γ M (Prop'.atom n)) :
    Indistinguishable ℓLow (Prop'.atom n) M M :=
  t3_atomic_fundamental ℓLow Γ M (Prop'.atom n) d

/-- Self-indistinguishability of well-typed terms. Formerly advertised
as "T3 — non-interference (canonical form)"; it is not (see the section
note): the body is one-run reflexivity, the derivation is discarded,
and ill-typed terms satisfy the conclusion equally. Kept under its
historical name so the ledger and axiom snapshots track it, with the
ledger reporting T3 as `stated`, not proven. -/
def T3_NonInterferenceStatement : Prop :=
  ∀ (ℓLow : Label) (Γₐ : List Prop') (M : Term) (φ : Prop'),
    PropDeriv Γₐ M φ → Indistinguishable ℓLow φ M M

/-- Discharge of the (weak) statement above by reflexivity. The
`PropDeriv` evidence is ignored — which is precisely why this is not
non-interference. The two-run T3 is open; see the section note. -/
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
