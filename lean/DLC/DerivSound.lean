/-
# A boolean valuation model of `Deriv` — the missing NEGATIVE direction.

The corpus proves `Deriv Γ M φ → …` everywhere but can never prove a judgment
**underivable** — there is no semantics to contradict a would-be derivation
against. This file supplies the smallest such semantics: a classical boolean
valuation `evalProp : Prop' → (Nat → Bool) → Bool` and a satisfaction relation
`satisfies` over `Ctx`. `DerivSound` (next increment) proves
`Deriv Γ M φ → satisfies Γ v → evalProp φ v = true`; then a valuation that makes
the hypotheses true and the conclusion false witnesses non-derivability
(`attenuate` converse, revocation, consistency).

## Why a *boolean* (classical) model is sound for the WHOLE calculus

`Deriv` is a linear/modal natural-deduction system, but every one of its rules
is a *restriction* of a classical inference: forgetting resource discipline and
modalities turns any `Deriv` proof into a classical one, which the boolean model
validates. So `evalProp` interprets the multiplicatives classically
(`tensor := ∧`, `lolli := →`) and the modalities transparently
(`says p φ`, `within τ φ`, `at φ ℓ`, `boxed O φ`, `replicated φ ℓ` all `:= φ`;
`speaksFor := ⊤`). This LOSES the ability to separate `∧` from `⊗` — deliberately;
the model exists to refute derivations, and a coarser (more permissive) model
refutes *more* soundly (if the coarse model already rejects `φ`, no finer one
derives it). Prior art: soundness by induction, each rule preserving the
valuation (Intuitionistic Propositional Logic in Lean, arXiv 2410.23765;
FormalizedFormalLogic/Foundation).
-/
import DLC.Judgment

namespace DLC

/-- Classical boolean truth of a proposition under an atom valuation `v`.
Multiplicatives collapse to their additive twins; modalities are transparent. -/
def evalProp : Prop' → (Nat → Bool) → Bool
  | Prop'.top, _ => true
  | Prop'.bot, _ => false
  | Prop'.atom n, v => v n
  | Prop'.imp φ ψ, v => (! evalProp φ v) || evalProp ψ v
  | Prop'.and φ ψ, v => evalProp φ v && evalProp ψ v
  | Prop'.or φ ψ, v => evalProp φ v || evalProp ψ v
  | Prop'.says _ φ, v => evalProp φ v
  | Prop'.speaksFor _ _, _ => true
  | Prop'.at φ _, v => evalProp φ v
  | Prop'.boxed _ φ, v => evalProp φ v
  | Prop'.within _ φ, v => evalProp φ v
  | Prop'.tensor φ ψ, v => evalProp φ v && evalProp ψ v
  | Prop'.lolli φ ψ, v => (! evalProp φ v) || evalProp ψ v
  | Prop'.replicated φ _, v => evalProp φ v

/-- A context is satisfied by `v` when EVERY hypothesis — additive and linear
alike — is true. (The boolean model forgets the additive/linear distinction, so
both lists are read as ordinary assumptions.) -/
def satisfies (Γ : Ctx) (v : Nat → Bool) : Prop :=
  (∀ φ, φ ∈ Γ.additive → evalProp φ v = true) ∧
  (∀ φ, φ ∈ Γ.linear → evalProp φ v = true)

/-- `Ctx.empty` is satisfied by every valuation. -/
theorem satisfies_empty (v : Nat → Bool) : satisfies Ctx.empty v := by
  refine ⟨?_, ?_⟩ <;> intro φ h <;> simp [Ctx.empty] at h

/-- Satisfaction of an additive-extended context splits into the head and tail. -/
theorem satisfies_consA {Γ : Ctx} {φ : Prop'} {v : Nat → Bool} :
    satisfies (Ctx.consA φ Γ) v ↔ evalProp φ v = true ∧ satisfies Γ v := by
  simp only [satisfies, Ctx.consA]
  constructor
  · intro ⟨ha, hl⟩
    refine ⟨ha φ (List.mem_cons_self ..), ?_, hl⟩
    intro ψ hψ
    exact ha ψ (List.mem_cons_of_mem _ hψ)
  · intro ⟨hφ, ha, hl⟩
    refine ⟨?_, hl⟩
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hφ
    · exact ha ψ hψ

/-- The additive hypotheses of a satisfied context are all true. -/
theorem satisfies_additive {Γ : Ctx} {v : Nat → Bool} (h : satisfies Γ v) :
    ∀ φ, φ ∈ Γ.additive → evalProp φ v = true := h.1

/-- The linear hypotheses of a satisfied context are all true. -/
theorem satisfies_linear {Γ : Ctx} {v : Nat → Bool} (h : satisfies Γ v) :
    ∀ φ, φ ∈ Γ.linear → evalProp φ v = true := h.2

/-- A satisfied append-linear context satisfies each half — the split `impE` /
`tensorI` / `discharge` need to apply both premise IHs. -/
theorem satisfies_linear_append {Γₐ Γ₁ Γ₂ : List Prop'} {v : Nat → Bool}
    (h : satisfies { additive := Γₐ, linear := Γ₁ ++ Γ₂ } v) :
    satisfies { additive := Γₐ, linear := Γ₁ } v ∧
    satisfies { additive := Γₐ, linear := Γ₂ } v := by
  simp only [satisfies] at h ⊢
  obtain ⟨ha, hl⟩ := h
  refine ⟨⟨ha, ?_⟩, ⟨ha, ?_⟩⟩
  · intro φ hφ; exact hl φ (List.mem_append.2 (Or.inl hφ))
  · intro φ hφ; exact hl φ (List.mem_append.2 (Or.inr hφ))

/-- Anti-vacuity: `evalProp` genuinely discriminates — `atom 0` is true under a
valuation setting it true and false under one setting it false. -/
theorem evalProp_discriminates :
    evalProp (Prop'.atom 0) (fun _ => true) = true ∧
    evalProp (Prop'.atom 0) (fun _ => false) = false :=
  ⟨rfl, rfl⟩

end DLC
