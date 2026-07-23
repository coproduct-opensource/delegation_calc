/-
T3, first rung — TWO-RUN non-interference for the introduction
fragment, at syntactic strength.

Design: `spec/t3-two-run-design-2026-07.md`. In one line: for
introduction-only derivations with an ℓLow-observable conclusion, the
proof term cannot reference any high-labeled hypothesis — so any two
instantiations of the high hypotheses yield LITERALLY EQUAL terms.
That is a genuine two-run statement (the observable output is
independent of high inputs), on a fragment small enough to avoid the
reduction-closure machinery the full theorem needs (see the design
doc's rung ladder), and the typing derivation is load-bearing — unlike
the retired reflexivity lemmas in `DLC.NonInterference`.

What this file does NOT claim: anything about elimination forms
(`fst (pair low high)` reaches a low type through a high intermediate
— handling that is the LR-redesign rung), or about `declassify`
(excluded by the fragment; unrestricted declassification falsifies
non-interference, as it must).
-/

import DLC.Judgment
import DLC.IFCLabel
import DLC.Subst
import DLC.Decidability

namespace DLC

/-! ## Observability at a label -/

/-- `Observable ℓLow φ`: every part of `φ` is visible to an observer
at `ℓLow`. `at φ ℓ` requires `ℓ ≤ ℓLow`; all other connectives are
structural. A context slot whose proposition is NOT observable is a
"high" hypothesis. -/
def Observable (ℓLow : Label) : Prop' → Prop
  | .top => True
  | .bot => True
  | .atom _ => True
  | .speaksFor _ _ => True
  | .at φ ℓ => Label.le ℓ ℓLow = true ∧ Observable ℓLow φ
  | .says _ φ => Observable ℓLow φ
  | .boxed _ φ => Observable ℓLow φ
  | .within _ φ => Observable ℓLow φ
  | .and φ ψ => Observable ℓLow φ ∧ Observable ℓLow ψ
  | .or φ ψ => Observable ℓLow φ ∧ Observable ℓLow ψ
  | .tensor φ ψ => Observable ℓLow φ ∧ Observable ℓLow ψ
  | .imp φ ψ => Observable ℓLow φ ∧ Observable ℓLow ψ
  | .lolli φ ψ => Observable ℓLow φ ∧ Observable ℓLow ψ
  | .replicated φ _ => Observable ℓLow φ

/-! ## Free-variable occurrence -/

/-- `usesVar M i`: the free de-Bruijn index `i` occurs in `M`
(cutoff-adjusted under binders: `lam`/`case` bind one, `letSays` one,
`letTensor` two). -/
def usesVar : Term → Nat → Bool
  | .var j, i => j == i
  | .lam _ b, i => usesVar b (i + 1)
  | .app f x, i => usesVar f i || usesVar x i
  | .sign _ m _, i => usesVar m i
  | .verify _ m _, i => usesVar m i
  | .delegate m n, i => usesVar m i || usesVar n i
  | .attenuate m _, i => usesVar m i
  | .boxed _ m n, i => usesVar m i || usesVar n i
  | .discharge m n, i => usesVar m i || usesVar n i
  | .liftLabel _ m, i => usesVar m i
  | .declassify _ m π, i => usesVar m i || usesVar π i
  | .now _, _ => false
  | .withinIntro _ m, i => usesVar m i
  | .pair a b, i => usesVar a i || usesVar b i
  | .fst a, i => usesVar a i
  | .snd a, i => usesVar a i
  | .inl _ a, i => usesVar a i
  | .inr _ a, i => usesVar a i
  | .case s l r, i => usesVar s i || usesVar l (i + 1) || usesVar r (i + 1)
  | .tensorIntro a b, i => usesVar a i || usesVar b i
  | .letTensor s b, i => usesVar s i || usesVar b (i + 2)
  | .saysBind _ s b, i => usesVar s i || usesVar b (i + 1)
  | .letSays _ s b, i => usesVar s i || usesVar b (i + 1)
  | .sfExtract m, i => usesVar m i
  -- command(M, c, ℓ): non-binder subterms, occurrence at the same index.
  | .command m c _, i => usesVar m i || usesVar c i
  -- runCmd(V, s): non-binder subterms, occurrence at the same index.
  | .runCmd v s, i => usesVar v i || usesVar s i

/-- No free variable at or above `k` (indices below `k` may occur). -/
def ClosedAbove (t : Term) (k : Nat) : Prop :=
  ∀ i, k ≤ i → usesVar t i = false

/-- No free variables at all. -/
def Closed (t : Term) : Prop := ClosedAbove t 0

/-- Substitution at an unused index does not depend on the value: both
runs produce the same term. This is the syntactic heart of the two-run
corollary. -/
theorem substAt_indep {M : Term} :
    ∀ {i : Nat}, usesVar M i = false →
      ∀ (N₁ N₂ : Term), substAt M N₁ i = substAt M N₂ i := by
  induction M with
  | var j =>
      intro i h N₁ N₂
      simp only [usesVar, beq_eq_false_iff_ne, ne_eq] at h
      simp only [substAt, if_neg h]
  | lam p b ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | app f x ihf ihx =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihf h.1 N₁ N₂, ihx h.2 N₁ N₂]
  | sign p m sig ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | verify p m sig ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | delegate m n ihm ihn =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihm h.1 N₁ N₂, ihn h.2 N₁ N₂]
  | attenuate m ψ ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | boxed o m n ihm ihn =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihm h.1 N₁ N₂, ihn h.2 N₁ N₂]
  | discharge m n ihm ihn =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihm h.1 N₁ N₂, ihn h.2 N₁ N₂]
  | liftLabel l m ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | declassify l m π ihm ihπ =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihm h.1 N₁ N₂, ihπ h.2 N₁ N₂]
  | now t =>
      intro i _ N₁ N₂
      simp only [substAt]
  | withinIntro t m ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | pair a b iha ihb =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, iha h.1 N₁ N₂, ihb h.2 N₁ N₂]
  | fst a ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | snd a ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | inl p a ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | inr p a ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | case s l r ihs ihl ihr =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihs h.1.1 N₁ N₂, ihl h.1.2 N₁ N₂, ihr h.2 N₁ N₂]
  | tensorIntro a b iha ihb =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, iha h.1 N₁ N₂, ihb h.2 N₁ N₂]
  | letTensor s b ihs ihb =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihs h.1 N₁ N₂, ihb h.2 N₁ N₂]
  | saysBind p s b ihs ihb =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihs h.1 N₁ N₂, ihb h.2 N₁ N₂]
  | letSays p s b ihs ihb =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihs h.1 N₁ N₂, ihb h.2 N₁ N₂]
  | sfExtract m ih =>
      intro i h N₁ N₂
      simp only [usesVar] at h
      simp only [substAt, ih h N₁ N₂]
  | command m c l ihm ihc =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihm h.1 N₁ N₂, ihc h.2 N₁ N₂]
  | runCmd v s ihv ihs =>
      intro i h N₁ N₂
      simp only [usesVar, Bool.or_eq_false_iff] at h
      simp only [substAt, ihv h.1 N₁ N₂, ihs h.2 N₁ N₂]

/-! ## The introduction fragment -/

/-- Introduction-only derivations: every premise type is an immediate
subformula of the conclusion type, so observability propagates into
the induction without cut elimination. Mirrors the corresponding
`PropDeriv` rules exactly (see `IntroDeriv.toPropDeriv`). -/
inductive IntroDeriv : List Prop' → Term → Prop' → Type where
  | varA (Γₐ : List Prop') (i : Nat) (φ : Prop')
      (h : Γₐ[i]? = some φ) :
      IntroDeriv Γₐ (Term.var i) φ
  | saysI (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
      (sig : Signature)
      (d : IntroDeriv Γₐ M φ) :
      IntroDeriv Γₐ (Term.sign p M sig) (Prop'.says p φ)
  | andI (Γₐ : List Prop') (φ ψ : Prop') (a b : Term)
      (dA : IntroDeriv Γₐ a φ) (dB : IntroDeriv Γₐ b ψ) :
      IntroDeriv Γₐ (Term.pair a b) (Prop'.and φ ψ)
  | orI_L (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : IntroDeriv Γₐ a φ) :
      IntroDeriv Γₐ (Term.inl ψ a) (Prop'.or φ ψ)
  | orI_R (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : IntroDeriv Γₐ a ψ) :
      IntroDeriv Γₐ (Term.inr φ a) (Prop'.or φ ψ)
  | tensorI (Γₐ : List Prop') (φ ψ : Prop') (a b : Term)
      (dA : IntroDeriv Γₐ a φ) (dB : IntroDeriv Γₐ b ψ) :
      IntroDeriv Γₐ (Term.tensorIntro a b) (Prop'.tensor φ ψ)
  | withinI (Γₐ : List Prop') (τ : TimeBound) (φ : Prop') (M : Term)
      (d : IntroDeriv Γₐ M φ) :
      IntroDeriv Γₐ (Term.withinIntro τ M) (Prop'.within τ φ)
  | liftLabel (Γₐ : List Prop') (φ : Prop') (ℓ : Label) (M : Term)
      (d : IntroDeriv Γₐ M φ) :
      IntroDeriv Γₐ (Term.liftLabel ℓ M) (Prop'.at φ ℓ)
  | now (Γₐ : List Prop') (τ : TimeBound) :
      IntroDeriv Γₐ (Term.now τ) Prop'.top

/-- The fragment embeds into `PropDeriv` (hence into the calculus):
these are honest restrictions of the real rules, not a parallel
system. -/
noncomputable def IntroDeriv.toPropDeriv {Γₐ : List Prop'} {M : Term}
    {φ : Prop'} (d : IntroDeriv Γₐ M φ) : PropDeriv Γₐ M φ := by
  induction d with
  | varA i φ h => exact .varA _ i φ h
  | saysI p φ M sig _ ih => exact .saysI _ p φ M sig ih
  | andI φ ψ a b _ _ ihA ihB => exact .andI _ φ ψ a b ihA ihB
  | orI_L φ ψ a _ ih => exact .orI_L _ φ ψ a ih
  | orI_R φ ψ a _ ih => exact .orI_R _ φ ψ a ih
  | tensorI φ ψ a b _ _ ihA ihB => exact .tensorI _ φ ψ a b ihA ihB
  | withinI τ φ M _ ih => exact .withinI _ τ φ M ih
  | liftLabel φ ℓ M _ ih => exact .liftLabel _ φ ℓ M ih
  | now τ => exact .now _ τ

/-! ## Confinement: observable conclusions cannot touch high inputs -/

/-- T3 first rung, confinement form. If an introduction-only
derivation concludes an ℓLow-OBSERVABLE proposition, its proof term
references no HIGH hypothesis (context slot with a non-observable
proposition). The typing derivation is load-bearing: the `varA` case
turns observability of the conclusion into observability of the
referenced slot, contradicting highness. -/
theorem t3_intro_confinement (ℓLow : Label)
    {Γₐ : List Prop'} {M : Term} {φ : Prop'}
    (d : IntroDeriv Γₐ M φ) (hobs : Observable ℓLow φ) :
    ∀ (i : Nat) (ψ : Prop'), Γₐ[i]? = some ψ →
      ¬ Observable ℓLow ψ → usesVar M i = false := by
  induction d with
  | varA j φ h =>
      intro i ψ hslot hhigh
      simp only [usesVar, beq_eq_false_iff_ne, ne_eq]
      intro hji
      subst hji
      rw [h] at hslot
      exact hhigh (Option.some.inj hslot ▸ hobs)
  | saysI p φ M sig _ ih =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simpa [usesVar] using ih hobs i ψ hslot hhigh
  | andI φ ψ2 a b _ _ ihA ihB =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simp only [usesVar, Bool.or_eq_false_iff]
      exact ⟨ihA hobs.1 i ψ hslot hhigh, ihB hobs.2 i ψ hslot hhigh⟩
  | orI_L φ ψ2 a _ ih =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simpa [usesVar] using ih hobs.1 i ψ hslot hhigh
  | orI_R φ ψ2 a _ ih =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simpa [usesVar] using ih hobs.2 i ψ hslot hhigh
  | tensorI φ ψ2 a b _ _ ihA ihB =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simp only [usesVar, Bool.or_eq_false_iff]
      exact ⟨ihA hobs.1 i ψ hslot hhigh, ihB hobs.2 i ψ hslot hhigh⟩
  | withinI τ φ M _ ih =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simpa [usesVar] using ih hobs i ψ hslot hhigh
  | liftLabel φ ℓ M _ ih =>
      intro i ψ hslot hhigh
      simp only [Observable] at hobs
      simpa [usesVar] using ih hobs.2 i ψ hslot hhigh
  | now τ =>
      intro i ψ _ _
      rfl

/-! ## The two-run theorem -/

/-- T3 first rung, two-run form. Let the hypothesis at slot 0 be HIGH
(not ℓLow-observable) and the conclusion OBSERVABLE. Then the two runs
of `M` under ANY two instantiations `N₁`, `N₂` of that hypothesis are
literally equal: the observable output is independent of the high
input. Non-interference for the introduction fragment, at syntactic
strength. -/
theorem t3_intro_two_run (ℓLow : Label)
    {Γₐ : List Prop'} {M : Term} {φ ψ : Prop'}
    (d : IntroDeriv (ψ :: Γₐ) M φ)
    (hobs : Observable ℓLow φ) (hhigh : ¬ Observable ℓLow ψ)
    (N₁ N₂ : Term) :
    substAt M N₁ 0 = substAt M N₂ 0 := by
  have hunused : usesVar M 0 = false :=
    t3_intro_confinement ℓLow d hobs 0 ψ rfl hhigh
  exact substAt_indep hunused N₁ N₂

end DLC
