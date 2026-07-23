/-
T3 rung 3c, stage 2 — THE FUNDAMENTAL LEMMA of the two-run logical
relation, and its corollaries.

Design: `spec/t3-two-run-design-2026-07.md`. The statement: every
`PropDeriv` derivation in the computational core (`CoreTerm`) maps
`LRel`-related closed environments (`EnvRel`) to `LRel`-related
substitution instances. Its two corollaries are the real T3:

* `lrel_self` — reflexivity of the PER on well-typed closed core
  terms (the diagonal γ₁ = γ₂), which `DLC.NonInterferenceLR`
  deliberately did NOT provide for free;
* `t3_two_run_general` — an observable-typed core computation cannot
  distinguish two arbitrary closed instantiations of a HIGH
  hypothesis: the high slot's `at`-gate (`ℓhigh ⋠ ℓLow`) makes ANY
  two closed terms related there.

Proof shape, per typing rule: distribute `msubst` over the subject's
constructor (`msubstAt_*`), then

* introduction rules — the introduction form IS the value the
  relation's ∃-form demands (`Steps.refl` reducts) with the premise
  IHs as payloads;
* elimination rules — the scrutinee IH yields value-shaped reducts;
  lift the scrutinee path through the ξ-congruence lemma, append the
  head β-step, close under anti-reduction (`lrel_expand`), commute
  the binder substitution past the environment
  (`msubstAt_substAt_comm(_gen)`), and apply the branch IH under the
  extended environment;
* frozen eliminations (verify / attenuate / declassify / discharge)
  — excluded by the core gate, necessarily: they produce stuck
  non-values that no relation over reduction can connect.
-/

import DLC.Progress
import DLC.NonInterferenceLR
import DLC.NonInterferenceEnv

namespace DLC

/-- THE FUNDAMENTAL LEMMA (T3, rung 3c). Every derivation in the
computational core maps LRel-related closed environments to
LRel-related substitution instances. Reflexivity of `LRel` on
well-typed closed core terms is the diagonal (γ₁ = γ₂). Frozen
eliminations (verify/attenuate/declassify/discharge) are excluded by
the core gate — necessarily: they produce stuck non-values that no
relation over reduction can connect. -/
theorem fundamental (ℓLow : Label) {Γₐ : List Prop'} {M : Term} {φ : Prop'}
    (d : PropDeriv Γₐ M φ) (hcore : CoreTerm M = true) :
    ∀ {γ₁ γ₂ : List Term}, EnvRel ℓLow Γₐ γ₁ γ₂ →
      LRel ℓLow φ (msubst M γ₁) (msubst M γ₂) := by
  revert hcore
  induction d with
  | varA Γ i χ h =>
      intro _ γ₁ γ₂ henv
      exact henv.lookup h
  | impI Γ χ ψ M' dbody ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_lam, Nat.zero_add]
      simp only [LRel]
      intro X Y hX hY hXY
      refine lrel_expand_left ℓLow ψ rfl ?_
      refine lrel_expand_right ℓLow ψ rfl ?_
      have h₁ : subst (msubstAt M' γ₁ 1) X = msubstAt (subst M' X) γ₁ 0 :=
        msubstAt_substAt_comm hX γ₁ M' 0
      have h₂ : subst (msubstAt M' γ₂ 1) Y = msubstAt (subst M' Y) γ₂ 0 :=
        msubstAt_substAt_comm hY γ₂ M' 0
      rw [h₁, h₂]
      exact ih hcore (EnvRel.cons hXY hX hY henv)
  | impE Γ χ ψ M' N dM dN ihM ihN =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      have harr := ihM hcore.1 henv
      simp only [LRel] at harr
      have hX : Closed (msubst N γ₁) :=
        msubst_closes henv.closed_left
          (by rw [henv.length_left]; exact propDeriv_fvar_bound dN)
      have hY : Closed (msubst N γ₂) :=
        msubst_closes henv.closed_right
          (by rw [henv.length_right]; exact propDeriv_fvar_bound dN)
      simp only [msubst, msubstAt_app]
      exact harr _ _ hX hY (ihN hcore.2 henv)
  | saysI Γ p χ M' sig dM ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_sign]
      exact ⟨_, _, _, _, .refl _, .refl _, ih hcore henv⟩
  | verifyE Γ p χ M' sig dM ih =>
      intro hcore
      simp [CoreTerm] at hcore
  | andI Γ χ ψ a b dA dB ihA ihB =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      simp only [msubst, msubstAt_pair]
      exact ⟨lrel_expand_left ℓLow χ rfl
               (lrel_expand_right ℓLow χ rfl (ihA hcore.1 henv)),
             lrel_expand_left ℓLow ψ rfl
               (lrel_expand_right ℓLow ψ rfl (ihB hcore.2 henv))⟩
  | andEL Γ χ ψ a dA ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_fst]
      exact (ih hcore henv).1
  | andER Γ χ ψ a dA ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_snd]
      exact (ih hcore henv).2
  | withinI Γ τ χ M' dM ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_withinIntro]
      exact ⟨_, _, .refl _, .refl _, ih hcore henv⟩
  | orI_L Γ χ ψ a dA ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_inl]
      exact Or.inl ⟨_, _, _, _, .refl _, .refl _, ih hcore henv⟩
  | orI_R Γ χ ψ a dA ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_inr]
      exact Or.inr ⟨_, _, _, _, .refl _, .refl _, ih hcore henv⟩
  | tensorI Γ χ ψ a b dA dB ihA ihB =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      simp only [msubst, msubstAt_tensorIntro]
      exact ⟨_, _, _, _, .refl _, .refl _, ihA hcore.1 henv, ihB hcore.2 henv⟩
  | orE Γ χ ψ ρ S L R dS dL dR ihS ihL ihR =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      obtain ⟨⟨hcS, hcL⟩, hcR⟩ := hcore
      simp only [msubst, msubstAt_case, Nat.zero_add]
      have hclosed₁ : Closed (msubst S γ₁) :=
        msubst_closes henv.closed_left
          (by rw [henv.length_left]; exact propDeriv_fvar_bound dS)
      have hclosed₂ : Closed (msubst S γ₂) :=
        msubst_closes henv.closed_right
          (by rw [henv.length_right]; exact propDeriv_fvar_bound dS)
      rcases ihS hcS henv with
        ⟨χ₁, χ₂, a₁, a₂, hS₁, hS₂, hp⟩ | ⟨χ₁, χ₂, a₁, a₂, hS₁, hS₂, hp⟩
      · -- inl: land on the L-branch redex on both sides.
        have hca₁ : Closed a₁ :=
          closed_of_closed_inl (steps_preserves_closed hS₁ hclosed₁)
        have hca₂ : Closed a₂ :=
          closed_of_closed_inl (steps_preserves_closed hS₂ hclosed₂)
        have hpath₁ : Steps
            (Term.case (msubstAt S γ₁ 0) (msubstAt L γ₁ 1) (msubstAt R γ₁ 1))
            (subst (msubstAt L γ₁ 1) a₁) :=
          (steps_congr
            (F := fun t => Term.case t (msubstAt L γ₁ 1) (msubstAt R γ₁ 1))
            (fun h => step_case_congr h) hS₁).trans (Steps.single rfl)
        have hpath₂ : Steps
            (Term.case (msubstAt S γ₂ 0) (msubstAt L γ₂ 1) (msubstAt R γ₂ 1))
            (subst (msubstAt L γ₂ 1) a₂) :=
          (steps_congr
            (F := fun t => Term.case t (msubstAt L γ₂ 1) (msubstAt R γ₂ 1))
            (fun h => step_case_congr h) hS₂).trans (Steps.single rfl)
        refine lrel_expand ℓLow ρ hpath₁ hpath₂ ?_
        have h₁ : subst (msubstAt L γ₁ 1) a₁ = msubstAt (subst L a₁) γ₁ 0 :=
          msubstAt_substAt_comm hca₁ γ₁ L 0
        have h₂ : subst (msubstAt L γ₂ 1) a₂ = msubstAt (subst L a₂) γ₂ 0 :=
          msubstAt_substAt_comm hca₂ γ₂ L 0
        rw [h₁, h₂]
        exact ihL hcL (EnvRel.cons hp hca₁ hca₂ henv)
      · -- inr: symmetric, R-branch.
        have hca₁ : Closed a₁ :=
          closed_of_closed_inr (steps_preserves_closed hS₁ hclosed₁)
        have hca₂ : Closed a₂ :=
          closed_of_closed_inr (steps_preserves_closed hS₂ hclosed₂)
        have hpath₁ : Steps
            (Term.case (msubstAt S γ₁ 0) (msubstAt L γ₁ 1) (msubstAt R γ₁ 1))
            (subst (msubstAt R γ₁ 1) a₁) :=
          (steps_congr
            (F := fun t => Term.case t (msubstAt L γ₁ 1) (msubstAt R γ₁ 1))
            (fun h => step_case_congr h) hS₁).trans (Steps.single rfl)
        have hpath₂ : Steps
            (Term.case (msubstAt S γ₂ 0) (msubstAt L γ₂ 1) (msubstAt R γ₂ 1))
            (subst (msubstAt R γ₂ 1) a₂) :=
          (steps_congr
            (F := fun t => Term.case t (msubstAt L γ₂ 1) (msubstAt R γ₂ 1))
            (fun h => step_case_congr h) hS₂).trans (Steps.single rfl)
        refine lrel_expand ℓLow ρ hpath₁ hpath₂ ?_
        have h₁ : subst (msubstAt R γ₁ 1) a₁ = msubstAt (subst R a₁) γ₁ 0 :=
          msubstAt_substAt_comm hca₁ γ₁ R 0
        have h₂ : subst (msubstAt R γ₂ 1) a₂ = msubstAt (subst R a₂) γ₂ 0 :=
          msubstAt_substAt_comm hca₂ γ₂ R 0
        rw [h₁, h₂]
        exact ihR hcR (EnvRel.cons hp hca₁ hca₂ henv)
  | letSaysE Γ p χ ψ S B dS dB ihS ihB =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      simp only [msubst, msubstAt_letSays, Nat.zero_add]
      have hclosed₁ : Closed (msubst S γ₁) :=
        msubst_closes henv.closed_left
          (by rw [henv.length_left]; exact propDeriv_fvar_bound dS)
      have hclosed₂ : Closed (msubst S γ₂) :=
        msubst_closes henv.closed_right
          (by rw [henv.length_right]; exact propDeriv_fvar_bound dS)
      obtain ⟨m₁, σ₁, m₂, σ₂, hS₁, hS₂, hp⟩ := ihS hcore.1 henv
      have hcm₁ : Closed m₁ :=
        closed_of_closed_sign (steps_preserves_closed hS₁ hclosed₁)
      have hcm₂ : Closed m₂ :=
        closed_of_closed_sign (steps_preserves_closed hS₂ hclosed₂)
      have hhead₁ : step (Term.letSays p (Term.sign p m₁ σ₁) (msubstAt B γ₁ 1))
          = some (subst (msubstAt B γ₁ 1) m₁) := by
        simp [step]
      have hhead₂ : step (Term.letSays p (Term.sign p m₂ σ₂) (msubstAt B γ₂ 1))
          = some (subst (msubstAt B γ₂ 1) m₂) := by
        simp [step]
      have hpath₁ : Steps (Term.letSays p (msubstAt S γ₁ 0) (msubstAt B γ₁ 1))
          (subst (msubstAt B γ₁ 1) m₁) :=
        (steps_congr (F := fun t => Term.letSays p t (msubstAt B γ₁ 1))
          (fun h => step_letSays_congr h) hS₁).trans (Steps.single hhead₁)
      have hpath₂ : Steps (Term.letSays p (msubstAt S γ₂ 0) (msubstAt B γ₂ 1))
          (subst (msubstAt B γ₂ 1) m₂) :=
        (steps_congr (F := fun t => Term.letSays p t (msubstAt B γ₂ 1))
          (fun h => step_letSays_congr h) hS₂).trans (Steps.single hhead₂)
      refine lrel_expand ℓLow ψ hpath₁ hpath₂ ?_
      have h₁ : subst (msubstAt B γ₁ 1) m₁ = msubstAt (subst B m₁) γ₁ 0 :=
        msubstAt_substAt_comm hcm₁ γ₁ B 0
      have h₂ : subst (msubstAt B γ₂ 1) m₂ = msubstAt (subst B m₂) γ₂ 0 :=
        msubstAt_substAt_comm hcm₂ γ₂ B 0
      rw [h₁, h₂]
      exact ihB hcore.2 (EnvRel.cons hp hcm₁ hcm₂ henv)
  | sfExtractE Γ p q M' dM ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_sfExtract]
      obtain ⟨m₁, σ₁, m₂, σ₂, hS₁, hS₂, hp⟩ := ih hcore henv
      obtain ⟨V, pV₁, pV₂⟩ := hp
      exact ⟨V,
        ((steps_congr (F := fun t => Term.sfExtract t)
          (fun h => step_sfExtract_congr h) hS₁).trans
            (Steps.single rfl)).trans pV₁,
        ((steps_congr (F := fun t => Term.sfExtract t)
          (fun h => step_sfExtract_congr h) hS₂).trans
            (Steps.single rfl)).trans pV₂⟩
  | delegate Γ p q χ M' N dM dN ihM ihN =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      simp only [msubst, msubstAt_delegate]
      obtain ⟨u₁, σ₁, u₂, σ₂, hM₁, hM₂, -⟩ := ihM hcore.1 henv
      obtain ⟨v₁, τ₁, v₂, τ₂, hN₁, hN₂, hpv⟩ := ihN hcore.2 henv
      have hpath₁ : Steps (Term.delegate (msubstAt M' γ₁ 0) (msubstAt N γ₁ 0))
          (Term.sign (Principal.acting p q) v₁ τ₁) :=
        (((steps_congr (F := fun t => Term.delegate t (msubstAt N γ₁ 0))
            (fun h => step_delegate_left_congr h) hM₁).trans
          (steps_congr (F := fun t => Term.delegate (Term.sign p u₁ σ₁) t)
            (fun h => step_delegate_right_congr h) hN₁)).trans
          (Steps.single rfl))
      have hpath₂ : Steps (Term.delegate (msubstAt M' γ₂ 0) (msubstAt N γ₂ 0))
          (Term.sign (Principal.acting p q) v₂ τ₂) :=
        (((steps_congr (F := fun t => Term.delegate t (msubstAt N γ₂ 0))
            (fun h => step_delegate_left_congr h) hM₂).trans
          (steps_congr (F := fun t => Term.delegate (Term.sign p u₂ σ₂) t)
            (fun h => step_delegate_right_congr h) hN₂)).trans
          (Steps.single rfl))
      exact ⟨v₁, τ₁, v₂, τ₂, hpath₁, hpath₂, hpv⟩
  | now Γ τ =>
      intro _ γ₁ γ₂ _
      trivial
  | attenuate Γ p χ M' dM ih =>
      intro hcore
      simp [CoreTerm] at hcore
  | liftLabel Γ χ ℓ M' dM ih =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm] at hcore
      simp only [msubst, msubstAt_liftLabel]
      simp only [LRel]
      split
      · exact ⟨_, _, .refl _, .refl _, ih hcore henv⟩
      · trivial
  | declassify Γ χ ℓ ℓ' M' π dM dπ ihM ihπ =>
      intro hcore
      simp [CoreTerm] at hcore
  | discharge Γ O χ M' N dM dN ihM ihN =>
      intro hcore
      simp [CoreTerm] at hcore
  | letTensor Γ χ ψ ρ S B dS dB ihS ihB =>
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      simp only [msubst, msubstAt_letTensor, Nat.zero_add]
      have hclosed₁ : Closed (msubst S γ₁) :=
        msubst_closes henv.closed_left
          (by rw [henv.length_left]; exact propDeriv_fvar_bound dS)
      have hclosed₂ : Closed (msubst S γ₂) :=
        msubst_closes henv.closed_right
          (by rw [henv.length_right]; exact propDeriv_fvar_bound dS)
      obtain ⟨a₁, b₁, a₂, b₂, hS₁, hS₂, hpa, hpb⟩ := ihS hcore.1 henv
      have hcT₁ := steps_preserves_closed hS₁ hclosed₁
      have hcT₂ := steps_preserves_closed hS₂ hclosed₂
      have hca₁ : Closed a₁ := closed_of_closed_tensorIntro_left hcT₁
      have hcb₁ : Closed b₁ := closed_of_closed_tensorIntro_right hcT₁
      have hca₂ : Closed a₂ := closed_of_closed_tensorIntro_left hcT₂
      have hcb₂ : Closed b₂ := closed_of_closed_tensorIntro_right hcT₂
      have hpath₁ : Steps
          (Term.letTensor (msubstAt S γ₁ 0) (msubstAt B γ₁ 2))
          (subst (subst (msubstAt B γ₁ 2) (shift a₁ 1 0)) b₁) :=
        (steps_congr (F := fun t => Term.letTensor t (msubstAt B γ₁ 2))
          (fun h => step_letTensor_congr h) hS₁).trans (Steps.single rfl)
      have hpath₂ : Steps
          (Term.letTensor (msubstAt S γ₂ 0) (msubstAt B γ₂ 2))
          (subst (subst (msubstAt B γ₂ 2) (shift a₂ 1 0)) b₂) :=
        (steps_congr (F := fun t => Term.letTensor t (msubstAt B γ₂ 2))
          (fun h => step_letTensor_congr h) hS₂).trans (Steps.single rfl)
      refine lrel_expand ℓLow ρ hpath₁ hpath₂ ?_
      rw [shift_closed hca₁ 1 0, shift_closed hca₂ 1 0]
      -- TWO commutations per side: first pull `a` (index 0 under depth 2,
      -- i.e. (e, d) = (0, 1)), then pull `b` (the standard e = d = 0 case).
      have h₁ : subst (msubstAt B γ₁ 2) a₁ = msubstAt (subst B a₁) γ₁ 1 :=
        msubstAt_substAt_comm_gen hca₁ γ₁ (Nat.zero_le 1) B
      have h₁' : subst (msubstAt (subst B a₁) γ₁ 1) b₁
          = msubstAt (subst (subst B a₁) b₁) γ₁ 0 :=
        msubstAt_substAt_comm hcb₁ γ₁ (subst B a₁) 0
      have h₂ : subst (msubstAt B γ₂ 2) a₂ = msubstAt (subst B a₂) γ₂ 1 :=
        msubstAt_substAt_comm_gen hca₂ γ₂ (Nat.zero_le 1) B
      have h₂' : subst (msubstAt (subst B a₂) γ₂ 1) b₂
          = msubstAt (subst (subst B a₂) b₂) γ₂ 0 :=
        msubstAt_substAt_comm hcb₂ γ₂ (subst B a₂) 0
      rw [h₁, h₁', h₂, h₂']
      exact ihB hcore.2
        (EnvRel.cons hpa hca₁ hca₂ (EnvRel.cons hpb hcb₁ hcb₂ henv))
  | commitI Γₐ issuer capProp φ ℓ M c dc dM ih_c ih_M =>
      -- commit-I (design §5.2). `command M c ℓ` is a VALUE, so both
      -- substitution instances step to themselves (`.refl`); the intro-form
      -- `Replicated` clause then reduces the goal to relating the
      -- store-transformer payloads at `φ⊃φ` — exactly the payload IH `ih_M`.
      -- The credential and label are transparent to the low observer.
      intro hcore γ₁ γ₂ henv
      simp only [CoreTerm, Bool.and_eq_true] at hcore
      simp only [msubst, msubstAt_command]
      exact ⟨_, _, _, _, _, _, .refl _, .refl _, ih_M hcore.1 henv⟩

/-! ## Corollaries -/

/-- Reflexivity on well-typed closed core terms — the diagonal. This is
exactly the reflexivity `DLC.NonInterferenceLR` refused to grant for
free: it holds only BECAUSE the term is well-typed and core. -/
theorem lrel_self (ℓLow : Label) {M : Term} {φ : Prop'}
    (d : PropDeriv [] M φ) (hcore : CoreTerm M = true) :
    LRel ℓLow φ M M :=
  fundamental ℓLow d hcore EnvRel.nil

/-- T3, TWO-RUN FORM: an observable-typed computation in the core cannot
distinguish two arbitrary closed instantiations of a HIGH hypothesis
(label ⋠ ℓLow), given closed well-typed core low inputs for the rest. -/
theorem t3_two_run_general (ℓLow : Label) {Γrest : List Prop'} {M : Term}
    {φ χ : Prop'} {ℓhigh : Label}
    (d : PropDeriv ((Prop'.at χ ℓhigh) :: Γrest) M φ)
    (hcore : CoreTerm M = true)
    (hhigh : Label.le ℓhigh ℓLow = false)
    {N₁ N₂ : Term} (hN₁ : Closed N₁) (hN₂ : Closed N₂)
    {γ : List Term} (hγ : EnvRel ℓLow Γrest γ γ) :
    LRel ℓLow φ (msubst M (N₁ :: γ)) (msubst M (N₂ :: γ)) := by
  have hgate : LRel ℓLow (Prop'.at χ ℓhigh) N₁ N₂ := by
    simp only [LRel]
    rw [if_neg (by simp [hhigh])]
    trivial
  exact fundamental ℓLow d hcore (EnvRel.cons hgate hN₁ hN₂ hγ)

end DLC
