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

/-- Extend the ADDITIVE part of an (explicit-record) satisfied context by a true prop. -/
theorem satisfies_consA_ctx {Γₐ Γₗ : List Prop'} {v : Nat → Bool} {φ : Prop'}
    (hφ : evalProp φ v = true)
    (h : satisfies { additive := Γₐ, linear := Γₗ } v) :
    satisfies { additive := φ :: Γₐ, linear := Γₗ } v := by
  obtain ⟨ha, hl⟩ := h
  exact ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ hφ) (ha x), hl⟩

/-- Extend the LINEAR part of an (explicit-record) satisfied context by a true prop. -/
theorem satisfies_consL_ctx {Γₐ Γₗ : List Prop'} {v : Nat → Bool} {φ : Prop'}
    (hφ : evalProp φ v = true)
    (h : satisfies { additive := Γₐ, linear := Γₗ } v) :
    satisfies { additive := Γₐ, linear := φ :: Γₗ } v := by
  obtain ⟨ha, hl⟩ := h
  exact ⟨ha, fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ hφ) (hl x)⟩

/-- Anti-vacuity: `evalProp` genuinely discriminates — `atom 0` is true under a
valuation setting it true and false under one setting it false. -/
theorem evalProp_discriminates :
    evalProp (Prop'.atom 0) (fun _ => true) = true ∧
    evalProp (Prop'.atom 0) (fun _ => false) = false :=
  ⟨rfl, rfl⟩

/-- **`Deriv` is sound for the boolean model.** Every derivable proposition is true under any
valuation satisfying its context. This is the NEGATIVE-direction engine: a valuation making the
hypotheses true and the conclusion false witnesses underivability (`attenuate` converse, revocation,
consistency). Sound for the WHOLE calculus — linear/modal rules are restrictions of classical ones,
so reading the linear context additively still yields a true conclusion; even `commit-I` (concludes
`replicated (φ ⊃ φ)`, a tautology) and `runCmd` (`φ` from its store premise) go through. -/
theorem deriv_sound {Γ : Ctx} {M : Term} {φ : Prop'} (v : Nat → Bool) :
    Deriv Γ M φ → satisfies Γ v → evalProp φ v = true := by
  intro d
  induction d with
  | varA Γ i φ hlook =>
    intro h; exact satisfies_additive h φ (List.mem_of_getElem? hlook)
  | varL Γₐ φ =>
    intro h; exact satisfies_linear h φ (List.mem_cons_self ..)
  | weakenA Γ φ' φ M _ ih =>
    intro h; exact ih (satisfies_consA.1 h).2
  | impI Γ φ ψ M _ ih =>
    intro h
    simp only [evalProp]
    cases hφ : evalProp φ v with
    | false => simp
    | true => have := ih (satisfies_consA.2 ⟨hφ, h⟩); simp [this]
  | impE Γₐ Γ₁ Γ₂ φ ψ M N _ _ ihM ihN =>
    intro h
    obtain ⟨h1, h2⟩ := satisfies_linear_append h
    have hM := ihM h1; have hN := ihN h2
    simp only [evalProp, hN, Bool.not_true, Bool.false_or] at hM
    exact hM
  | saysI Γ p φ M sig _ ih => intro h; simpa only [evalProp] using ih h
  | verifyE Γ p φ M sig _ ih => intro h; simpa only [evalProp] using ih h
  | saysE Γₐ Γ₁ Γ₂ p φ ψ M N _ _ ihM ihN =>
    intro h
    obtain ⟨h1, h2⟩ := satisfies_linear_append h
    have hM := ihM h1
    simp only [evalProp] at hM ⊢
    exact ihN (satisfies_consA_ctx hM h2)
  | delegate Γₐ Γ₁ Γ₂ p q φ M N _ _ _ ihN =>
    intro h
    obtain ⟨_, h2⟩ := satisfies_linear_append h
    have hN := ihN h2
    simpa only [evalProp] using hN
  | attenuate Γ p φ ψ M N _ _ ihd ihimpl =>
    intro h
    have hd := ihd h
    simp only [evalProp] at hd ⊢
    exact ihimpl (satisfies_consA.2 ⟨hd, satisfies_empty v⟩)
  | boxI Γ O φ M N _ _ ihM _ => intro h; simpa only [evalProp] using ihM h
  | discharge Γₐ Γ₁ Γ₂ O φ M N _ _ ihM _ =>
    intro h
    obtain ⟨h1, _⟩ := satisfies_linear_append h
    have hM := ihM h1
    simpa only [evalProp] using hM
  | now Γₐ τ => intro _; rfl
  | withinI Γ τ φ M _ ih => intro h; simpa only [evalProp] using ih h
  | withinE Γ τ φ M _ ih => intro h; simpa only [evalProp] using ih h
  | liftLabel Γ φ ℓ M _ ih => intro h; simpa only [evalProp] using ih h
  | declassify Γ φ ℓ ℓ' M π _ _ ihd _ =>
    intro h; simpa only [evalProp] using ihd h
  | andI Γₐ φ ψ M N _ _ ihM ihN =>
    intro h; simp only [evalProp, ihM h, ihN h, Bool.and_self]
  | andEL Γ φ ψ M _ ih =>
    intro h; have := ih h; simp only [evalProp, Bool.and_eq_true] at this; exact this.1
  | andER Γ φ ψ M _ ih =>
    intro h; have := ih h; simp only [evalProp, Bool.and_eq_true] at this; exact this.2
  | orI_L Γ φ ψ M _ ih =>
    intro h; simp only [evalProp, ih h, Bool.true_or]
  | orI_R Γ φ ψ M _ ih =>
    intro h; simp only [evalProp, ih h, Bool.or_true]
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
    intro h
    have hS := ihS h; simp only [evalProp, Bool.or_eq_true] at hS
    rcases hS with hφ | hψ
    · exact ihL (satisfies_consA_ctx hφ h)
    · exact ihR (satisfies_consA_ctx hψ h)
  | tensorI Γₐ Γ₁ Γ₂ φ ψ M N _ _ ihM ihN =>
    intro h
    obtain ⟨h1, h2⟩ := satisfies_linear_append h
    simp only [evalProp, ihM h1, ihN h2, Bool.and_self]
  | tensorE Γₐ Γ₁ Γ₂ φ ψ χ S B _ _ ihS ihB =>
    intro h
    obtain ⟨h1, h2⟩ := satisfies_linear_append h
    have hS := ihS h1; simp only [evalProp, Bool.and_eq_true] at hS
    exact ihB (satisfies_consL_ctx hS.2 (satisfies_consL_ctx hS.1 h2))
  | letTensorA Γₐ φ ψ χ S B _ _ ihS ihB =>
    intro h
    have hS := ihS h; simp only [evalProp, Bool.and_eq_true] at hS
    exact ihB (satisfies_consA_ctx hS.1 (satisfies_consA_ctx hS.2 h))
  | letSaysE Γₐ Γ₁ Γ₂ p φ ψ S B _ _ ihS ihB =>
    intro h
    obtain ⟨h1, h2⟩ := satisfies_linear_append h
    have hS := ihS h1; simp only [evalProp] at hS
    exact ihB (satisfies_consA_ctx hS h2)
  | sfExtractE Γ p q M _ _ => intro _; rfl
  | commitI Γₐ issuer capProp φ ℓ M c _ _ _ _ =>
    intro _; simp only [evalProp]; cases hb : evalProp φ v <;> simp
  | runCmd Γₐ φ ℓ V s _ _ _ ihs =>
    intro h; simpa only [evalProp] using ihs h

/-- Non-vacuity: a real derivation whose `evalProp` conclusion soundness fires — the identity
`a ⊃ a` in the empty context is derivable and evaluates to `true` under every valuation. -/
theorem deriv_sound_witness (v : Nat → Bool) :
    evalProp (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) v = true :=
  deriv_sound v
    (Deriv.impI Ctx.empty (Prop'.atom 0) (Prop'.atom 0) (Term.var 0)
      (Deriv.varA _ 0 _ rfl))
    (satisfies_empty v)

/-! ## The NEGATIVE direction — underivability from soundness.

`deriv_sound` gives the first consistency corollaries: a valuation that satisfies the hypotheses but
falsifies the conclusion proves NO derivation exists. The prototype is `atom 1 ⊬ atom 0`, from which
the `attenuate` CONVERSE (a genuine widening is underivable) falls out — closing the fence
`attenuate_only_narrows` left open (spec/interop-says-biscuit.md §2; positioning-doc §5). -/

/-- The valuation separating atom 0 (true) from atom 1 (false). -/
private def sep : Nat → Bool := fun n => n == 0

/-- **`atom 1` is NOT derivable from `atom 0`.** The prototype underivability result: `sep` satisfies
the hypothesis `atom 0` but falsifies `atom 1`, so soundness forbids any derivation. -/
theorem atom_not_derivable_from_atom :
    ¬ ∃ N, Nonempty (Deriv (Ctx.consA (Prop'.atom 0) Ctx.empty) N (Prop'.atom 1)) := by
  rintro ⟨N, ⟨d⟩⟩
  have hsat : satisfies (Ctx.consA (Prop'.atom 0) Ctx.empty) sep :=
    satisfies_consA.2 ⟨rfl, satisfies_empty _⟩
  have h := deriv_sound sep d hsat
  simp [evalProp, sep] at h

/-- **A genuine widening is underivable.** `p says (atom 1)` cannot be concluded from a hypothesis
`p says (atom 0)` — by ANY subject term. This is the `Deriv`-level converse of `attenuate_only_narrows`:
narrowing carries a witness (proved there); widening has none (proved here). Subject-agnostic, so it a
fortiori rules out an `attenuate` node — see `attenuate_cannot_widen`. -/
theorem widening_says_underivable (p : Principal) :
    ¬ ∃ M, Nonempty (Deriv (Ctx.consA (Prop'.says p (Prop'.atom 0)) Ctx.empty) M
             (Prop'.says p (Prop'.atom 1))) := by
  rintro ⟨M, ⟨d⟩⟩
  have hsat : satisfies (Ctx.consA (Prop'.says p (Prop'.atom 0)) Ctx.empty) sep :=
    satisfies_consA.2 ⟨rfl, satisfies_empty _⟩
  have h := deriv_sound sep d hsat
  simp [evalProp, sep] at h

/-- **`attenuate` cannot widen.** No `attenuate _ (atom 1)` node concludes `p says (atom 1)` from a
`p says (atom 0)` hypothesis — the right-reason bite completing the attenuation-narrowing story:
narrowing is always witnessed (`attenuate_only_narrows`), widening is impossible (here). -/
theorem attenuate_cannot_widen (p : Principal) :
    ¬ ∃ M, Nonempty (Deriv (Ctx.consA (Prop'.says p (Prop'.atom 0)) Ctx.empty)
             (Term.attenuate M (Prop'.atom 1)) (Prop'.says p (Prop'.atom 1))) := by
  rintro ⟨M, hd⟩
  exact widening_says_underivable p ⟨_, hd⟩

end DLC
