/-
T3 rung 3c, stage 1 — closedness and simultaneous-substitution
infrastructure for the fundamental lemma.

Design: `spec/t3-two-run-design-2026-07.md`. The fundamental lemma
(rung 3c stage 2) states that a `PropDeriv`-typed term, closed by two
`LRel`-related environments, is self-related. This file supplies the
three ingredient stacks that statement consumes:

1. CLOSEDNESS — `ClosedAbove`/`Closed`, their interaction with `shift`
   and `substAt` (closed terms are fixed points), the fact that
   substituting a closed value lowers the free-variable bound
   (`substAt_closes_gen`), and preservation of closedness under
   reduction (`step_preserves_closed`, `steps_preserves_closed`).

2. SIMULTANEOUS SUBSTITUTION — `msubstAt`/`msubst` apply a list of
   (intended-closed) substituents head-first at a fixed depth.
   Distribution lemmas over every constructor, the variable-resolution
   lemma (`msubst_var`), THE binder-commutation lemma
   (`msubstAt_substAt_comm`, one `substAt_substAt` per element), and
   closedness of the result (`msubst_closes`).

3. TYPING/ENVIRONMENT GLUE — well-typed terms use only variables below
   the context length (`propDeriv_fvar_bound`), and `EnvRel`, the
   pointwise `LRel`-related closed environments, with the packaged
   variable case of the fundamental lemma (`EnvRel.lookup`).
-/

import DLC.Subst
import DLC.Reduce
import DLC.ReduceMeta
import DLC.Decidability
import DLC.NonInterferenceTwoRun
import DLC.NonInterferenceLR

namespace DLC

/-! ## Closedness -/

-- `ClosedAbove` / `Closed` live in `DLC.NonInterferenceTwoRun`
-- (usesVar's home) so `DLC.NonInterferenceLR` can use them without an
-- import cycle.

theorem closed_closedAbove {t : Term} {k : Nat} (h : Closed t) : ClosedAbove t k :=
  fun i _ => h i (Nat.zero_le i)

/-! ### Pointwise characterizations, one per constructor.

`ClosedAbove` of a composite term is the conjunction of `ClosedAbove`
of its components, with binders bumping the bound (`lam`/`case`
branches/`letSays` body +1, `letTensor` body +2) exactly as `usesVar`
bumps its cutoff. Non-binder cases are one `simp` each; binder cases
need the index gymnastics spelled out once here so the induction
proofs below stay mechanical. -/

theorem closedAbove_var_iff {j k : Nat} : ClosedAbove (Term.var j) k ↔ j < k := by
  simp only [ClosedAbove, usesVar, beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro h
    by_contra hnot
    exact h j (by omega) rfl
  · intro h i hi
    omega

theorem closedAbove_lam_iff {φ : Prop'} {b : Term} {k : Nat} :
    ClosedAbove (Term.lam φ b) k ↔ ClosedAbove b (k + 1) := by
  constructor
  · intro h i hi
    have h' := h (i - 1) (by omega)
    simp only [usesVar] at h'
    rwa [show i - 1 + 1 = i from by omega] at h'
  · intro h i hi
    simp only [usesVar]
    exact h (i + 1) (by omega)

theorem closedAbove_app_iff {f x : Term} {k : Nat} :
    ClosedAbove (Term.app f x) k ↔ ClosedAbove f k ∧ ClosedAbove x k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_sign_iff {p : Principal} {m : Term} {σ : Signature} {k : Nat} :
    ClosedAbove (Term.sign p m σ) k ↔ ClosedAbove m k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_verify_iff {p : Principal} {m : Term} {σ : Signature} {k : Nat} :
    ClosedAbove (Term.verify p m σ) k ↔ ClosedAbove m k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_delegate_iff {m n : Term} {k : Nat} :
    ClosedAbove (Term.delegate m n) k ↔ ClosedAbove m k ∧ ClosedAbove n k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_attenuate_iff {m : Term} {ψ : Prop'} {k : Nat} :
    ClosedAbove (Term.attenuate m ψ) k ↔ ClosedAbove m k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_boxed_iff {o : Obligation} {m n : Term} {k : Nat} :
    ClosedAbove (Term.boxed o m n) k ↔ ClosedAbove m k ∧ ClosedAbove n k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_discharge_iff {m n : Term} {k : Nat} :
    ClosedAbove (Term.discharge m n) k ↔ ClosedAbove m k ∧ ClosedAbove n k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_liftLabel_iff {ℓ : Label} {m : Term} {k : Nat} :
    ClosedAbove (Term.liftLabel ℓ m) k ↔ ClosedAbove m k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_declassify_iff {ℓ : Label} {m π : Term} {k : Nat} :
    ClosedAbove (Term.declassify ℓ m π) k ↔ ClosedAbove m k ∧ ClosedAbove π k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_now {τ : TimeBound} {k : Nat} : ClosedAbove (Term.now τ) k := by
  intro i _
  simp [usesVar]

theorem closedAbove_withinIntro_iff {τ : TimeBound} {m : Term} {k : Nat} :
    ClosedAbove (Term.withinIntro τ m) k ↔ ClosedAbove m k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_pair_iff {a b : Term} {k : Nat} :
    ClosedAbove (Term.pair a b) k ↔ ClosedAbove a k ∧ ClosedAbove b k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_fst_iff {a : Term} {k : Nat} :
    ClosedAbove (Term.fst a) k ↔ ClosedAbove a k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_snd_iff {a : Term} {k : Nat} :
    ClosedAbove (Term.snd a) k ↔ ClosedAbove a k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_inl_iff {χ : Prop'} {a : Term} {k : Nat} :
    ClosedAbove (Term.inl χ a) k ↔ ClosedAbove a k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_inr_iff {χ : Prop'} {a : Term} {k : Nat} :
    ClosedAbove (Term.inr χ a) k ↔ ClosedAbove a k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_case_iff {s l r : Term} {k : Nat} :
    ClosedAbove (Term.case s l r) k ↔
      ClosedAbove s k ∧ ClosedAbove l (k + 1) ∧ ClosedAbove r (k + 1) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · have h' := h i hi
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      exact h'.1.1
    · have h' := h (i - 1) (by omega)
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      have h'' := h'.1.2
      rwa [show i - 1 + 1 = i from by omega] at h''
    · have h' := h (i - 1) (by omega)
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      have h'' := h'.2
      rwa [show i - 1 + 1 = i from by omega] at h''
  · rintro ⟨hs, hl, hr⟩ i hi
    simp only [usesVar, Bool.or_eq_false_iff]
    exact ⟨⟨hs i hi, hl (i + 1) (by omega)⟩, hr (i + 1) (by omega)⟩

theorem closedAbove_tensorIntro_iff {a b : Term} {k : Nat} :
    ClosedAbove (Term.tensorIntro a b) k ↔ ClosedAbove a k ∧ ClosedAbove b k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

theorem closedAbove_letTensor_iff {s b : Term} {k : Nat} :
    ClosedAbove (Term.letTensor s b) k ↔ ClosedAbove s k ∧ ClosedAbove b (k + 2) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h' := h i hi
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      exact h'.1
    · have h' := h (i - 2) (by omega)
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      have h'' := h'.2
      rwa [show i - 2 + 2 = i from by omega] at h''
  · rintro ⟨hs, hb⟩ i hi
    simp only [usesVar, Bool.or_eq_false_iff]
    exact ⟨hs i hi, hb (i + 2) (by omega)⟩

theorem closedAbove_saysBind_iff {p : Principal} {s b : Term} {k : Nat} :
    ClosedAbove (Term.saysBind p s b) k ↔ ClosedAbove s k ∧ ClosedAbove b (k + 1) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h' := h i hi
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      exact h'.1
    · have h' := h (i - 1) (by omega)
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      have h'' := h'.2
      rwa [show i - 1 + 1 = i from by omega] at h''
  · rintro ⟨hs, hb⟩ i hi
    simp only [usesVar, Bool.or_eq_false_iff]
    exact ⟨hs i hi, hb (i + 1) (by omega)⟩

theorem closedAbove_letSays_iff {p : Principal} {s b : Term} {k : Nat} :
    ClosedAbove (Term.letSays p s b) k ↔ ClosedAbove s k ∧ ClosedAbove b (k + 1) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h' := h i hi
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      exact h'.1
    · have h' := h (i - 1) (by omega)
      simp only [usesVar, Bool.or_eq_false_iff] at h'
      have h'' := h'.2
      rwa [show i - 1 + 1 = i from by omega] at h''
  · rintro ⟨hs, hb⟩ i hi
    simp only [usesVar, Bool.or_eq_false_iff]
    exact ⟨hs i hi, hb (i + 1) (by omega)⟩

theorem closedAbove_sfExtract_iff {m : Term} {k : Nat} :
    ClosedAbove (Term.sfExtract m) k ↔ ClosedAbove m k := by
  simp only [ClosedAbove, usesVar]

theorem closedAbove_command_iff {m c : Term} {ℓ : Label} {k : Nat} :
    ClosedAbove (Term.command m c ℓ) k ↔ ClosedAbove m k ∧ ClosedAbove c k := by
  simp only [ClosedAbove, usesVar, Bool.or_eq_false_iff, imp_and, forall_and]

/-! ### Closed terms are fixed points of `shift` and `substAt` -/

private theorem shift_closedAbove_aux (d : Nat) :
    ∀ (t : Term) (k c : Nat), ClosedAbove t k → k ≤ c → shift t d c = t := by
  intro t
  induction t with
  | var j =>
      intro k c h hc
      have hj : j < k := closedAbove_var_iff.mp h
      simp only [shift]
      rw [if_pos (show j < c by omega)]
  | lam p b ih =>
      intro k c h hc
      simp only [shift]
      rw [ih (k + 1) (c + 1) (closedAbove_lam_iff.mp h) (by omega)]
  | app f x ihf ihx =>
      intro k c h hc
      obtain ⟨hf, hx⟩ := closedAbove_app_iff.mp h
      simp only [shift]
      rw [ihf k c hf hc, ihx k c hx hc]
  | sign p m sig ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_sign_iff.mp h) hc]
  | verify p m sig ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_verify_iff.mp h) hc]
  | delegate m n ihm ihn =>
      intro k c h hc
      obtain ⟨hm, hn⟩ := closedAbove_delegate_iff.mp h
      simp only [shift]
      rw [ihm k c hm hc, ihn k c hn hc]
  | attenuate m ψ ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_attenuate_iff.mp h) hc]
  | boxed o m n ihm ihn =>
      intro k c h hc
      obtain ⟨hm, hn⟩ := closedAbove_boxed_iff.mp h
      simp only [shift]
      rw [ihm k c hm hc, ihn k c hn hc]
  | discharge m n ihm ihn =>
      intro k c h hc
      obtain ⟨hm, hn⟩ := closedAbove_discharge_iff.mp h
      simp only [shift]
      rw [ihm k c hm hc, ihn k c hn hc]
  | liftLabel l m ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_liftLabel_iff.mp h) hc]
  | declassify l m π ihm ihπ =>
      intro k c h hc
      obtain ⟨hm, hπ⟩ := closedAbove_declassify_iff.mp h
      simp only [shift]
      rw [ihm k c hm hc, ihπ k c hπ hc]
  | now t =>
      intro k c _ _
      simp only [shift]
  | withinIntro t m ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_withinIntro_iff.mp h) hc]
  | pair a b iha ihb =>
      intro k c h hc
      obtain ⟨ha, hb⟩ := closedAbove_pair_iff.mp h
      simp only [shift]
      rw [iha k c ha hc, ihb k c hb hc]
  | fst a ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_fst_iff.mp h) hc]
  | snd a ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_snd_iff.mp h) hc]
  | inl p a ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_inl_iff.mp h) hc]
  | inr p a ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_inr_iff.mp h) hc]
  | case s l r ihs ihl ihr =>
      intro k c h hc
      obtain ⟨hs, hl, hr⟩ := closedAbove_case_iff.mp h
      simp only [shift]
      rw [ihs k c hs hc, ihl (k + 1) (c + 1) hl (by omega),
          ihr (k + 1) (c + 1) hr (by omega)]
  | tensorIntro a b iha ihb =>
      intro k c h hc
      obtain ⟨ha, hb⟩ := closedAbove_tensorIntro_iff.mp h
      simp only [shift]
      rw [iha k c ha hc, ihb k c hb hc]
  | letTensor s b ihs ihb =>
      intro k c h hc
      obtain ⟨hs, hb⟩ := closedAbove_letTensor_iff.mp h
      simp only [shift]
      rw [ihs k c hs hc, ihb (k + 2) (c + 2) hb (by omega)]
  | saysBind p s b ihs ihb =>
      intro k c h hc
      obtain ⟨hs, hb⟩ := closedAbove_saysBind_iff.mp h
      simp only [shift]
      rw [ihs k c hs hc, ihb (k + 1) (c + 1) hb (by omega)]
  | letSays p s b ihs ihb =>
      intro k c h hc
      obtain ⟨hs, hb⟩ := closedAbove_letSays_iff.mp h
      simp only [shift]
      rw [ihs k c hs hc, ihb (k + 1) (c + 1) hb (by omega)]
  | sfExtract m ih =>
      intro k c h hc
      simp only [shift]
      rw [ih k c (closedAbove_sfExtract_iff.mp h) hc]
  | command m cr l ihm ihc =>
      intro k c h hc
      obtain ⟨hm, hcr⟩ := closedAbove_command_iff.mp h
      simp only [shift]
      rw [ihm k c hm hc, ihc k c hcr hc]

/-- Shifting above the free-variable bound is a no-op. -/
theorem shift_closedAbove {t : Term} {k : Nat} (h : ClosedAbove t k) (d c : Nat)
    (hc : k ≤ c) : shift t d c = t :=
  shift_closedAbove_aux d t k c h hc

/-- Shifting a closed term is a no-op. -/
theorem shift_closed {t : Term} (h : Closed t) (d c : Nat) : shift t d c = t :=
  shift_closedAbove (k := 0) h d c (Nat.zero_le c)

private theorem substAt_closedAbove_aux (v : Term) :
    ∀ (t : Term) (k i : Nat), ClosedAbove t k → k ≤ i → substAt t v i = t := by
  intro t
  induction t with
  | var j =>
      intro k i h hi
      have hj : j < k := closedAbove_var_iff.mp h
      exact substAt_var_lt v j i (by omega)
  | lam p b ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih (k + 1) (i + 1) (closedAbove_lam_iff.mp h) (by omega)]
  | app f x ihf ihx =>
      intro k i h hi
      obtain ⟨hf, hx⟩ := closedAbove_app_iff.mp h
      simp only [substAt]
      rw [ihf k i hf hi, ihx k i hx hi]
  | sign p m sig ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_sign_iff.mp h) hi]
  | verify p m sig ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_verify_iff.mp h) hi]
  | delegate m n ihm ihn =>
      intro k i h hi
      obtain ⟨hm, hn⟩ := closedAbove_delegate_iff.mp h
      simp only [substAt]
      rw [ihm k i hm hi, ihn k i hn hi]
  | attenuate m ψ ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_attenuate_iff.mp h) hi]
  | boxed o m n ihm ihn =>
      intro k i h hi
      obtain ⟨hm, hn⟩ := closedAbove_boxed_iff.mp h
      simp only [substAt]
      rw [ihm k i hm hi, ihn k i hn hi]
  | discharge m n ihm ihn =>
      intro k i h hi
      obtain ⟨hm, hn⟩ := closedAbove_discharge_iff.mp h
      simp only [substAt]
      rw [ihm k i hm hi, ihn k i hn hi]
  | liftLabel l m ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_liftLabel_iff.mp h) hi]
  | declassify l m π ihm ihπ =>
      intro k i h hi
      obtain ⟨hm, hπ⟩ := closedAbove_declassify_iff.mp h
      simp only [substAt]
      rw [ihm k i hm hi, ihπ k i hπ hi]
  | now t =>
      intro k i _ _
      simp only [substAt]
  | withinIntro t m ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_withinIntro_iff.mp h) hi]
  | pair a b iha ihb =>
      intro k i h hi
      obtain ⟨ha, hb⟩ := closedAbove_pair_iff.mp h
      simp only [substAt]
      rw [iha k i ha hi, ihb k i hb hi]
  | fst a ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_fst_iff.mp h) hi]
  | snd a ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_snd_iff.mp h) hi]
  | inl p a ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_inl_iff.mp h) hi]
  | inr p a ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_inr_iff.mp h) hi]
  | case s l r ihs ihl ihr =>
      intro k i h hi
      obtain ⟨hs, hl, hr⟩ := closedAbove_case_iff.mp h
      simp only [substAt]
      rw [ihs k i hs hi, ihl (k + 1) (i + 1) hl (by omega),
          ihr (k + 1) (i + 1) hr (by omega)]
  | tensorIntro a b iha ihb =>
      intro k i h hi
      obtain ⟨ha, hb⟩ := closedAbove_tensorIntro_iff.mp h
      simp only [substAt]
      rw [iha k i ha hi, ihb k i hb hi]
  | letTensor s b ihs ihb =>
      intro k i h hi
      obtain ⟨hs, hb⟩ := closedAbove_letTensor_iff.mp h
      simp only [substAt]
      rw [ihs k i hs hi, ihb (k + 2) (i + 2) hb (by omega)]
  | saysBind p s b ihs ihb =>
      intro k i h hi
      obtain ⟨hs, hb⟩ := closedAbove_saysBind_iff.mp h
      simp only [substAt]
      rw [ihs k i hs hi, ihb (k + 1) (i + 1) hb (by omega)]
  | letSays p s b ihs ihb =>
      intro k i h hi
      obtain ⟨hs, hb⟩ := closedAbove_letSays_iff.mp h
      simp only [substAt]
      rw [ihs k i hs hi, ihb (k + 1) (i + 1) hb (by omega)]
  | sfExtract m ih =>
      intro k i h hi
      simp only [substAt]
      rw [ih k i (closedAbove_sfExtract_iff.mp h) hi]
  | command m cr l ihm ihc =>
      intro k i h hi
      obtain ⟨hm, hcr⟩ := closedAbove_command_iff.mp h
      simp only [substAt]
      rw [ihm k i hm hi, ihc k i hcr hi]

/-- Substituting at or above the free-variable bound is a no-op. -/
theorem substAt_closedAbove {t : Term} {k : Nat} (h : ClosedAbove t k) (v : Term)
    {i : Nat} (hi : k ≤ i) : substAt t v i = t :=
  substAt_closedAbove_aux v t k i h hi

/-- Substituting into a closed term is a no-op. -/
theorem substAt_closed {t : Term} (h : Closed t) (v : Term) (i : Nat) :
    substAt t v i = t :=
  substAt_closedAbove (k := 0) h v (Nat.zero_le i)

/-! ### Substitution of closed values lowers the free-variable bound -/

/-- Generalized form: substituting a CLOSED value at any index `k` at or
below the bound `n` eliminates one free-variable slot — the result is
closed-above `n` if the original was closed-above `n + 1`. The
`k = n` instance is `substAt_closes`; the strict `k < n` instances are
what `msubst_closes` and the letTensor-β case of
`step_preserves_closed` fold over. -/
theorem substAt_closes_gen {v : Term} (hv : Closed v) :
    ∀ (b : Term) (n k : Nat), ClosedAbove b (n + 1) → k ≤ n →
      ClosedAbove (substAt b v k) n := by
  intro b
  induction b with
  | var j =>
      intro n k hb hk
      have hj : j < n + 1 := closedAbove_var_iff.mp hb
      rcases Nat.lt_trichotomy j k with hlt | rfl | hgt
      · rw [substAt_var_lt v j k hlt]
        exact closedAbove_var_iff.mpr (by omega)
      · rw [substAt_var_eq v j, shift_closed hv j 0]
        exact closed_closedAbove hv
      · rw [substAt_var_gt v j k hgt]
        exact closedAbove_var_iff.mpr (by omega)
  | lam p b ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_lam_iff.mpr
        (ih (n + 1) (k + 1) (closedAbove_lam_iff.mp hb) (by omega))
  | app f x ihf ihx =>
      intro n k hb hk
      obtain ⟨hf, hx⟩ := closedAbove_app_iff.mp hb
      simp only [substAt]
      exact closedAbove_app_iff.mpr ⟨ihf n k hf hk, ihx n k hx hk⟩
  | sign p m sig ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_sign_iff.mpr (ih n k (closedAbove_sign_iff.mp hb) hk)
  | verify p m sig ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_verify_iff.mpr (ih n k (closedAbove_verify_iff.mp hb) hk)
  | delegate m n' ihm ihn =>
      intro n k hb hk
      obtain ⟨hm, hn⟩ := closedAbove_delegate_iff.mp hb
      simp only [substAt]
      exact closedAbove_delegate_iff.mpr ⟨ihm n k hm hk, ihn n k hn hk⟩
  | attenuate m ψ ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_attenuate_iff.mpr (ih n k (closedAbove_attenuate_iff.mp hb) hk)
  | boxed o m n' ihm ihn =>
      intro n k hb hk
      obtain ⟨hm, hn⟩ := closedAbove_boxed_iff.mp hb
      simp only [substAt]
      exact closedAbove_boxed_iff.mpr ⟨ihm n k hm hk, ihn n k hn hk⟩
  | discharge m n' ihm ihn =>
      intro n k hb hk
      obtain ⟨hm, hn⟩ := closedAbove_discharge_iff.mp hb
      simp only [substAt]
      exact closedAbove_discharge_iff.mpr ⟨ihm n k hm hk, ihn n k hn hk⟩
  | liftLabel l m ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_liftLabel_iff.mpr (ih n k (closedAbove_liftLabel_iff.mp hb) hk)
  | declassify l m π ihm ihπ =>
      intro n k hb hk
      obtain ⟨hm, hπ⟩ := closedAbove_declassify_iff.mp hb
      simp only [substAt]
      exact closedAbove_declassify_iff.mpr ⟨ihm n k hm hk, ihπ n k hπ hk⟩
  | now t =>
      intro n k _ _
      simp only [substAt]
      exact closedAbove_now
  | withinIntro t m ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_withinIntro_iff.mpr
        (ih n k (closedAbove_withinIntro_iff.mp hb) hk)
  | pair a b iha ihb =>
      intro n k hb hk
      obtain ⟨ha, hb'⟩ := closedAbove_pair_iff.mp hb
      simp only [substAt]
      exact closedAbove_pair_iff.mpr ⟨iha n k ha hk, ihb n k hb' hk⟩
  | fst a ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_fst_iff.mpr (ih n k (closedAbove_fst_iff.mp hb) hk)
  | snd a ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_snd_iff.mpr (ih n k (closedAbove_snd_iff.mp hb) hk)
  | inl p a ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_inl_iff.mpr (ih n k (closedAbove_inl_iff.mp hb) hk)
  | inr p a ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_inr_iff.mpr (ih n k (closedAbove_inr_iff.mp hb) hk)
  | case s l r ihs ihl ihr =>
      intro n k hb hk
      obtain ⟨hs, hl, hr⟩ := closedAbove_case_iff.mp hb
      simp only [substAt]
      exact closedAbove_case_iff.mpr
        ⟨ihs n k hs hk, ihl (n + 1) (k + 1) hl (by omega),
         ihr (n + 1) (k + 1) hr (by omega)⟩
  | tensorIntro a b iha ihb =>
      intro n k hb hk
      obtain ⟨ha, hb'⟩ := closedAbove_tensorIntro_iff.mp hb
      simp only [substAt]
      exact closedAbove_tensorIntro_iff.mpr ⟨iha n k ha hk, ihb n k hb' hk⟩
  | letTensor s b ihs ihb =>
      intro n k hb hk
      obtain ⟨hs, hb'⟩ := closedAbove_letTensor_iff.mp hb
      simp only [substAt]
      exact closedAbove_letTensor_iff.mpr
        ⟨ihs n k hs hk, ihb (n + 2) (k + 2) hb' (by omega)⟩
  | saysBind p s b ihs ihb =>
      intro n k hb hk
      obtain ⟨hs, hb'⟩ := closedAbove_saysBind_iff.mp hb
      simp only [substAt]
      exact closedAbove_saysBind_iff.mpr
        ⟨ihs n k hs hk, ihb (n + 1) (k + 1) hb' (by omega)⟩
  | letSays p s b ihs ihb =>
      intro n k hb hk
      obtain ⟨hs, hb'⟩ := closedAbove_letSays_iff.mp hb
      simp only [substAt]
      exact closedAbove_letSays_iff.mpr
        ⟨ihs n k hs hk, ihb (n + 1) (k + 1) hb' (by omega)⟩
  | sfExtract m ih =>
      intro n k hb hk
      simp only [substAt]
      exact closedAbove_sfExtract_iff.mpr (ih n k (closedAbove_sfExtract_iff.mp hb) hk)
  | command m cr l ihm ihc =>
      intro n k hb hk
      obtain ⟨hm, hcr⟩ := closedAbove_command_iff.mp hb
      simp only [substAt]
      exact closedAbove_command_iff.mpr ⟨ihm n k hm hk, ihc n k hcr hk⟩

/-- Substituting a CLOSED value at index `k` eliminates that index and
lowers the ones above: the result is closed-above `k` if the original
was closed-above `k + 1`. -/
theorem substAt_closes {b : Term} {k : Nat} (v : Term) (hv : Closed v)
    (hb : ClosedAbove b (k + 1)) : ClosedAbove (substAt b v k) k :=
  substAt_closes_gen hv b k k hb (Nat.le_refl k)

theorem closed_subst {b v : Term} (hv : Closed v) (hb : ClosedAbove b 1) :
    Closed (subst b v) :=
  substAt_closes v hv hb

/-! ### Values' immediate subterms inherit closedness -/

theorem closed_of_closed_sign {p : Principal} {m : Term} {σ : Signature}
    (h : Closed (Term.sign p m σ)) : Closed m :=
  closedAbove_sign_iff.mp h

theorem closed_of_closed_pair_left {a b : Term} (h : Closed (Term.pair a b)) :
    Closed a :=
  (closedAbove_pair_iff.mp h).1

theorem closed_of_closed_pair_right {a b : Term} (h : Closed (Term.pair a b)) :
    Closed b :=
  (closedAbove_pair_iff.mp h).2

theorem closed_of_closed_inl {χ : Prop'} {a : Term} (h : Closed (Term.inl χ a)) :
    Closed a :=
  closedAbove_inl_iff.mp h

theorem closed_of_closed_inr {χ : Prop'} {a : Term} (h : Closed (Term.inr χ a)) :
    Closed a :=
  closedAbove_inr_iff.mp h

theorem closed_of_closed_tensorIntro_left {a b : Term}
    (h : Closed (Term.tensorIntro a b)) : Closed a :=
  (closedAbove_tensorIntro_iff.mp h).1

theorem closed_of_closed_tensorIntro_right {a b : Term}
    (h : Closed (Term.tensorIntro a b)) : Closed b :=
  (closedAbove_tensorIntro_iff.mp h).2

theorem closed_of_closed_withinIntro {τ : TimeBound} {m : Term}
    (h : Closed (Term.withinIntro τ m)) : Closed m :=
  closedAbove_withinIntro_iff.mp h

theorem closed_of_closed_liftLabel {ℓ : Label} {m : Term}
    (h : Closed (Term.liftLabel ℓ m)) : Closed m :=
  closedAbove_liftLabel_iff.mp h

/-! ### Spine components of closed elimination forms -/

theorem closed_of_closed_app_fun {f x : Term} (h : Closed (Term.app f x)) :
    Closed f :=
  (closedAbove_app_iff.mp h).1

theorem closed_of_closed_app_arg {f x : Term} (h : Closed (Term.app f x)) :
    Closed x :=
  (closedAbove_app_iff.mp h).2

theorem closed_of_closed_fst {a : Term} (h : Closed (Term.fst a)) : Closed a :=
  closedAbove_fst_iff.mp h

theorem closed_of_closed_snd {a : Term} (h : Closed (Term.snd a)) : Closed a :=
  closedAbove_snd_iff.mp h

theorem closed_of_closed_case_scrut {s l r : Term} (h : Closed (Term.case s l r)) :
    Closed s :=
  (closedAbove_case_iff.mp h).1

theorem closed_of_closed_delegate_left {m n : Term} (h : Closed (Term.delegate m n)) :
    Closed m :=
  (closedAbove_delegate_iff.mp h).1

theorem closed_of_closed_delegate_right {m n : Term} (h : Closed (Term.delegate m n)) :
    Closed n :=
  (closedAbove_delegate_iff.mp h).2

theorem closed_of_closed_saysBind_scrut {p : Principal} {s b : Term}
    (h : Closed (Term.saysBind p s b)) : Closed s :=
  (closedAbove_saysBind_iff.mp h).1

theorem closed_of_closed_letSays_scrut {p : Principal} {s b : Term}
    (h : Closed (Term.letSays p s b)) : Closed s :=
  (closedAbove_letSays_iff.mp h).1

theorem closed_of_closed_letTensor_scrut {s b : Term}
    (h : Closed (Term.letTensor s b)) : Closed s :=
  (closedAbove_letTensor_iff.mp h).1

theorem closed_of_closed_sfExtract {m : Term} (h : Closed (Term.sfExtract m)) :
    Closed m :=
  closedAbove_sfExtract_iff.mp h

/-! ### Bodies of closed binder forms are closed-above their binders -/

theorem closedAbove_of_closed_lam {φ : Prop'} {b : Term}
    (h : Closed (Term.lam φ b)) : ClosedAbove b 1 :=
  closedAbove_lam_iff.mp h

theorem closedAbove_of_closed_case_left {s l r : Term}
    (h : Closed (Term.case s l r)) : ClosedAbove l 1 :=
  (closedAbove_case_iff.mp h).2.1

theorem closedAbove_of_closed_case_right {s l r : Term}
    (h : Closed (Term.case s l r)) : ClosedAbove r 1 :=
  (closedAbove_case_iff.mp h).2.2

theorem closedAbove_of_closed_saysBind_body {p : Principal} {s b : Term}
    (h : Closed (Term.saysBind p s b)) : ClosedAbove b 1 :=
  (closedAbove_saysBind_iff.mp h).2

theorem closedAbove_of_closed_letSays_body {p : Principal} {s b : Term}
    (h : Closed (Term.letSays p s b)) : ClosedAbove b 1 :=
  (closedAbove_letSays_iff.mp h).2

theorem closedAbove_of_closed_letTensor_body {s b : Term}
    (h : Closed (Term.letTensor s b)) : ClosedAbove b 2 :=
  (closedAbove_letTensor_iff.mp h).2

/-! ### Reduction preserves closedness -/

private theorem step_preserves_closed_aux :
    ∀ (M M' : Term), step M = some M' → Closed M → Closed M' := by
  intro M
  induction M with
  | var _ => intro M' h _; simp [step] at h
  | lam _ _ _ => intro M' h _; simp [step] at h
  | app f x ihf _ =>
      intro M' h hc
      unfold step at h
      split at h
      · -- β: f = lam _ body, M' = subst body x.
        simp only [Option.some.injEq] at h
        subst h
        exact closed_subst (closed_of_closed_app_arg hc)
          (closedAbove_of_closed_lam (closed_of_closed_app_fun hc))
      · -- ξ-app.
        cases hf : step f with
        | none => simp [hf] at h
        | some f' =>
            simp [hf] at h
            subst h
            exact closedAbove_app_iff.mpr
              ⟨ihf f' hf (closed_of_closed_app_fun hc), closed_of_closed_app_arg hc⟩
  | sign _ _ _ _ => intro M' h _; simp [step] at h
  | verify _ _ _ _ => intro M' h _; simp [step] at h
  | delegate m n ihm ihn =>
      intro M' h hc
      unfold step at h
      split at h
      · -- delegate-β: M' = sign (acting p q) inner sig'.
        simp only [Option.some.injEq] at h
        subst h
        exact closedAbove_sign_iff.mpr
          (closed_of_closed_sign (closed_of_closed_delegate_right hc))
      · -- ξ-delegate (right): left is a sign and passes through.
        cases hn : step n with
        | none => simp [hn] at h
        | some n' =>
            simp [hn] at h
            subst h
            exact closedAbove_delegate_iff.mpr
              ⟨closed_of_closed_delegate_left hc,
               ihn n' hn (closed_of_closed_delegate_right hc)⟩
      · -- ξ-delegate (left).
        cases hm : step m with
        | none => simp [hm] at h
        | some m' =>
            simp [hm] at h
            subst h
            exact closedAbove_delegate_iff.mpr
              ⟨ihm m' hm (closed_of_closed_delegate_left hc),
               closed_of_closed_delegate_right hc⟩
  | attenuate _ _ _ => intro M' h _; simp [step] at h
  | boxed o _ _ _ _ => intro M' h _; simp [step] at h
  | discharge m p ihm _ =>
      -- No longer irreducible: R4 gave discharge a redex.
      intro M' h hc
      unfold step at h
      split at h
      · -- discharge-beta: m = boxed _ inner _, M' = inner. Closedness of
        -- the box's payload follows from closedness of the whole redex.
        simp only [Option.some.injEq] at h
        subst h
        exact (closedAbove_boxed_iff.mp (closedAbove_discharge_iff.mp hc).1).1
      · -- xi-discharge.
        cases hm : step m with
        | none => simp [hm] at h
        | some m' =>
            simp [hm] at h
            subst h
            exact closedAbove_discharge_iff.mpr
              ⟨ihm m' hm (closedAbove_discharge_iff.mp hc).1,
               (closedAbove_discharge_iff.mp hc).2⟩
  | liftLabel _ _ _ => intro M' h _; simp [step] at h
  | declassify _ _ _ _ _ => intro M' h _; simp [step] at h
  | now _ => intro M' h _; simp [step] at h
  | withinIntro _ _ _ => intro M' h _; simp [step] at h
  | pair _ _ _ _ => intro M' h _; simp [step] at h
  | fst a ih =>
      intro M' h hc
      unfold step at h
      split at h
      · -- and-Eₗ-β: a = pair u v, M' = u.
        simp only [Option.some.injEq] at h
        subst h
        exact closed_of_closed_pair_left (closed_of_closed_fst hc)
      · -- ξ-fst.
        cases ha : step a with
        | none => simp [ha] at h
        | some a' =>
            simp [ha] at h
            subst h
            exact closedAbove_fst_iff.mpr (ih a' ha (closed_of_closed_fst hc))
  | snd a ih =>
      intro M' h hc
      unfold step at h
      split at h
      · -- and-Eᵣ-β.
        simp only [Option.some.injEq] at h
        subst h
        exact closed_of_closed_pair_right (closed_of_closed_snd hc)
      · -- ξ-snd.
        cases ha : step a with
        | none => simp [ha] at h
        | some a' =>
            simp [ha] at h
            subst h
            exact closedAbove_snd_iff.mpr (ih a' ha (closed_of_closed_snd hc))
  | inl _ _ _ => intro M' h _; simp [step] at h
  | inr _ _ _ => intro M' h _; simp [step] at h
  | case s l r ihs _ _ =>
      intro M' h hc
      unfold step at h
      split at h
      · -- or-E-β (inl): M' = subst l a.
        simp only [Option.some.injEq] at h
        subst h
        exact closed_subst
          (closed_of_closed_inl (closed_of_closed_case_scrut hc))
          (closedAbove_of_closed_case_left hc)
      · -- or-E-β (inr): M' = subst r a.
        simp only [Option.some.injEq] at h
        subst h
        exact closed_subst
          (closed_of_closed_inr (closed_of_closed_case_scrut hc))
          (closedAbove_of_closed_case_right hc)
      · -- ξ-case.
        cases hs : step s with
        | none => simp [hs] at h
        | some s' =>
            simp [hs] at h
            subst h
            exact closedAbove_case_iff.mpr
              ⟨ihs s' hs (closed_of_closed_case_scrut hc),
               closedAbove_of_closed_case_left hc,
               closedAbove_of_closed_case_right hc⟩
  | tensorIntro _ _ _ _ => intro M' h _; simp [step] at h
  | letTensor s b ihs _ =>
      intro M' h hc
      unfold step at h
      split at h
      · -- tensor-E-β: M' = subst (subst b (shift a 1 0)) bb, with the
        -- scrutinee a ⊗ bb closed, so shift a 1 0 = a; then the inner
        -- substitution consumes index 0 of the 2-closed body at depth 0
        -- leaving a 1-closed term (substAt_closes_gen at n := 1, k := 0),
        -- and the outer substitution closes it.
        simp only [Option.some.injEq] at h
        subst h
        have hscrut := closed_of_closed_letTensor_scrut hc
        have ha := closed_of_closed_tensorIntro_left hscrut
        have hb := closed_of_closed_tensorIntro_right hscrut
        have hbody := closedAbove_of_closed_letTensor_body hc
        rw [shift_closed ha 1 0]
        exact closed_subst hb (substAt_closes_gen ha b 1 0 hbody (by omega))
      · -- ξ-lettensor.
        cases hs : step s with
        | none => simp [hs] at h
        | some s' =>
            simp [hs] at h
            subst h
            exact closedAbove_letTensor_iff.mpr
              ⟨ihs s' hs (closed_of_closed_letTensor_scrut hc),
               closedAbove_of_closed_letTensor_body hc⟩
  | saysBind p s b ihs _ =>
      intro M' h hc
      unfold step at h
      split at h
      · -- s = sign p' m sig; head rule guards on p = p'.
        split at h
        · -- says-extract-β: M' = subst b m.
          simp only [Option.some.injEq] at h
          subst h
          exact closed_subst
            (closed_of_closed_sign (closed_of_closed_saysBind_scrut hc))
            (closedAbove_of_closed_saysBind_body hc)
        · -- p ≠ p': step returned none — contradiction.
          simp at h
      · -- ξ-letsays.
        cases hs : step s with
        | none => simp [hs] at h
        | some s' =>
            simp [hs] at h
            subst h
            exact closedAbove_saysBind_iff.mpr
              ⟨ihs s' hs (closed_of_closed_saysBind_scrut hc),
               closedAbove_of_closed_saysBind_body hc⟩
  | letSays p s b ihs _ =>
      intro M' h hc
      unfold step at h
      split at h
      · -- s = sign p' m sig; head rule guards on p = p'.
        split at h
        · -- says-extract-β: M' = subst b m.
          simp only [Option.some.injEq] at h
          subst h
          exact closed_subst
            (closed_of_closed_sign (closed_of_closed_letSays_scrut hc))
            (closedAbove_of_closed_letSays_body hc)
        · -- p ≠ p': step returned none — contradiction.
          simp at h
      · -- ξ-letsays.
        cases hs : step s with
        | none => simp [hs] at h
        | some s' =>
            simp [hs] at h
            subst h
            exact closedAbove_letSays_iff.mpr
              ⟨ihs s' hs (closed_of_closed_letSays_scrut hc),
               closedAbove_of_closed_letSays_body hc⟩
  | sfExtract m ih =>
      intro M' h hc
      unfold step at h
      split at h
      · -- sf-extract-β: M' = inner.
        simp only [Option.some.injEq] at h
        subst h
        exact closed_of_closed_sign (closed_of_closed_sfExtract hc)
      · -- ξ-sfextract.
        cases hm : step m with
        | none => simp [hm] at h
        | some m' =>
            simp [hm] at h
            subst h
            exact closedAbove_sfExtract_iff.mpr
              (ih m' hm (closed_of_closed_sfExtract hc))
  -- command is STUCK: `step (command ..) = none`, so `step M = some M'` is
  -- impossible — vacuous, like the frozen `sign`/`verify` cases.
  | command _ _ _ _ _ => intro M' h _; simp [step] at h

/-- One reduction step preserves closedness. -/
theorem step_preserves_closed {M M' : Term} (h : step M = some M') (hc : Closed M) :
    Closed M' :=
  step_preserves_closed_aux M M' h hc

/-- Multi-step reduction preserves closedness. -/
theorem steps_preserves_closed {M M' : Term} (h : Steps M M') (hc : Closed M) :
    Closed M' := by
  induction h with
  | refl _ => exact hc
  | head hstep _ ih => exact ih (step_preserves_closed hstep hc)

/-! ## Simultaneous substitution -/

/-- Apply a list of (intended-closed) substituents at depth `d`, head first:
`γ[0]` replaces var `d`, then `γ[1]` replaces the NEW var `d` (originally
`d + 1`), …. -/
def msubstAt : Term → List Term → Nat → Term
  | M, [], _ => M
  | M, t :: γ, d => msubstAt (substAt M t d) γ d

/-- Closing substitution at depth 0. -/
def msubst (M : Term) (γ : List Term) : Term := msubstAt M γ 0

/-- All elements closed. -/
def ClosedEnv (γ : List Term) : Prop := ∀ t ∈ γ, Closed t

/-- Simultaneous substitution into a closed term is a no-op. -/
theorem msubstAt_closed {t : Term} (ht : Closed t) (γ : List Term) (d : Nat) :
    msubstAt t γ d = t := by
  induction γ with
  | nil => rfl
  | cons u γ' ih =>
      simp only [msubstAt]
      rw [substAt_closed ht u d]
      exact ih

/-! ### Distribution over every constructor -/

theorem msubstAt_app (f x : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.app f x) γ d = Term.app (msubstAt f γ d) (msubstAt x γ d) := by
  induction γ generalizing f x with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt f t d) (substAt x t d)

theorem msubstAt_sign (p : Principal) (m : Term) (σ : Signature)
    (γ : List Term) (d : Nat) :
    msubstAt (Term.sign p m σ) γ d = Term.sign p (msubstAt m γ d) σ := by
  induction γ generalizing m with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d)

theorem msubstAt_verify (p : Principal) (m : Term) (σ : Signature)
    (γ : List Term) (d : Nat) :
    msubstAt (Term.verify p m σ) γ d = Term.verify p (msubstAt m γ d) σ := by
  induction γ generalizing m with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d)

theorem msubstAt_delegate (m n : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.delegate m n) γ d
      = Term.delegate (msubstAt m γ d) (msubstAt n γ d) := by
  induction γ generalizing m n with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d) (substAt n t d)

theorem msubstAt_command (m c : Term) (ℓ : Label) (γ : List Term) (d : Nat) :
    msubstAt (Term.command m c ℓ) γ d
      = Term.command (msubstAt m γ d) (msubstAt c γ d) ℓ := by
  induction γ generalizing m c with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d) (substAt c t d)

theorem msubstAt_attenuate (m : Term) (ψ : Prop') (γ : List Term) (d : Nat) :
    msubstAt (Term.attenuate m ψ) γ d = Term.attenuate (msubstAt m γ d) ψ := by
  induction γ generalizing m with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d)

theorem msubstAt_discharge (m n : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.discharge m n) γ d
      = Term.discharge (msubstAt m γ d) (msubstAt n γ d) := by
  induction γ generalizing m n with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d) (substAt n t d)

theorem msubstAt_liftLabel (ℓ : Label) (m : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.liftLabel ℓ m) γ d = Term.liftLabel ℓ (msubstAt m γ d) := by
  induction γ generalizing m with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d)

theorem msubstAt_declassify (ℓ : Label) (m π : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.declassify ℓ m π) γ d
      = Term.declassify ℓ (msubstAt m γ d) (msubstAt π γ d) := by
  induction γ generalizing m π with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d) (substAt π t d)

theorem msubstAt_now (τ : TimeBound) (γ : List Term) (d : Nat) :
    msubstAt (Term.now τ) γ d = Term.now τ := by
  induction γ with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih

theorem msubstAt_withinIntro (τ : TimeBound) (m : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.withinIntro τ m) γ d = Term.withinIntro τ (msubstAt m γ d) := by
  induction γ generalizing m with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d)

theorem msubstAt_pair (a b : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.pair a b) γ d = Term.pair (msubstAt a γ d) (msubstAt b γ d) := by
  induction γ generalizing a b with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt a t d) (substAt b t d)

theorem msubstAt_fst (a : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.fst a) γ d = Term.fst (msubstAt a γ d) := by
  induction γ generalizing a with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt a t d)

theorem msubstAt_snd (a : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.snd a) γ d = Term.snd (msubstAt a γ d) := by
  induction γ generalizing a with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt a t d)

theorem msubstAt_inl (χ : Prop') (a : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.inl χ a) γ d = Term.inl χ (msubstAt a γ d) := by
  induction γ generalizing a with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt a t d)

theorem msubstAt_inr (χ : Prop') (a : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.inr χ a) γ d = Term.inr χ (msubstAt a γ d) := by
  induction γ generalizing a with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt a t d)

theorem msubstAt_tensorIntro (a b : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.tensorIntro a b) γ d
      = Term.tensorIntro (msubstAt a γ d) (msubstAt b γ d) := by
  induction γ generalizing a b with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt a t d) (substAt b t d)

theorem msubstAt_sfExtract (m : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.sfExtract m) γ d = Term.sfExtract (msubstAt m γ d) := by
  induction γ generalizing m with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt m t d)

/-! Binder constructors shift the depth. -/

theorem msubstAt_lam (φ : Prop') (b : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.lam φ b) γ d = Term.lam φ (msubstAt b γ (d + 1)) := by
  induction γ generalizing b with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt b t (d + 1))

theorem msubstAt_case (s l r : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.case s l r) γ d
      = Term.case (msubstAt s γ d) (msubstAt l γ (d + 1)) (msubstAt r γ (d + 1)) := by
  induction γ generalizing s l r with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt s t d) (substAt l t (d + 1)) (substAt r t (d + 1))

theorem msubstAt_letSays (p : Principal) (s b : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.letSays p s b) γ d
      = Term.letSays p (msubstAt s γ d) (msubstAt b γ (d + 1)) := by
  induction γ generalizing s b with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt s t d) (substAt b t (d + 1))

theorem msubstAt_letTensor (s b : Term) (γ : List Term) (d : Nat) :
    msubstAt (Term.letTensor s b) γ d
      = Term.letTensor (msubstAt s γ d) (msubstAt b γ (d + 2)) := by
  induction γ generalizing s b with
  | nil => rfl
  | cons t γ' ih =>
      simp only [msubstAt, substAt]
      exact ih (substAt s t d) (substAt b t (d + 2))

/-! ### Variable resolution -/

/-- Substituting at depth 0 sends `var (i + 1)` to `var i` regardless of
the value (the "walk past the head" step of `msubst` on variables). -/
theorem substAt_var_succ (v : Term) (i : Nat) :
    substAt (Term.var (i + 1)) v 0 = Term.var i := by
  rw [substAt_var_gt v (i + 1) 0 (by omega), Nat.add_sub_cancel]

private theorem msubst_var_aux :
    ∀ (γ : List Term), ClosedEnv γ → ∀ (i : Nat) (t : Term), γ[i]? = some t →
      msubst (Term.var i) γ = t := by
  intro γ
  induction γ with
  | nil => intro _ i t hslot; simp at hslot
  | cons u γ' ih =>
      intro henv i t hslot
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hslot
          subst hslot
          simp only [msubst, msubstAt]
          rw [substAt_var_eq u 0, shift_zero]
          exact msubstAt_closed (henv u List.mem_cons_self) γ' 0
      | succ i' =>
          simp only [List.getElem?_cons_succ] at hslot
          simp only [msubst, msubstAt, substAt_var_succ]
          exact ih (fun s hs => henv s (List.mem_cons_of_mem u hs)) i' t hslot

/-- The var lemma at depth 0: a full closed environment resolves variables
to their entries. Stated hypothesis-style (`γ[i]? = some t`) because
`Term` carries no `Inhabited` instance for `getElem!`. -/
theorem msubst_var {γ : List Term} (henv : ClosedEnv γ) {i : Nat} {t : Term}
    (hslot : γ[i]? = some t) : msubst (Term.var i) γ = t :=
  msubst_var_aux γ henv i t hslot

/-! ### THE binder commutation -/

/-- Pulling a closed argument substitution under an `msubstAt` at the next
depth (one `substAt_substAt` per environment element). This is what lets
the fundamental lemma's binder cases β-reduce
`msubstAt (lam φ B) γ d` applied to an argument. -/
theorem msubstAt_substAt_comm {X : Term} (hX : Closed X) (γ : List Term) :
    ∀ (B : Term) (d : Nat), substAt (msubstAt B γ (d + 1)) X d
      = msubstAt (substAt B X d) γ d := by
  induction γ with
  | nil => intro B d; rfl
  | cons t γ' ih =>
      intro B d
      -- LHS = substAt (msubstAt (substAt B t (d+1)) γ' (d+1)) X d
      --     = msubstAt (substAt (substAt B t (d+1)) X d) γ' d          (IH)
      -- and substAt_substAt (j := d, k := d) turns the RHS's inner pair
      --   substAt (substAt B X d) t d
      -- into substAt (substAt B t (d+1)) (substAt X t 0) d, whose
      -- placed value collapses to X by closedness.
      simp only [msubstAt]
      rw [ih (substAt B t (d + 1)) d,
          substAt_substAt X t B d d (Nat.le_refl d),
          Nat.sub_self, substAt_closed hX t 0]

/-- Generalized binder commutation: pulling a closed substitution at any
index `e ≤ d` under an environment fold at depth `d+1`. (The `e = d`
case is `msubstAt_substAt_comm`; letTensor's two-binder redex needs
`(e, d) = (0, 1)`.) -/
theorem msubstAt_substAt_comm_gen {X : Term} (hX : Closed X) (γ : List Term)
    {e d : Nat} (hed : e ≤ d) :
    ∀ (B : Term), substAt (msubstAt B γ (d + 1)) X e
      = msubstAt (substAt B X e) γ d := by
  induction γ with
  | nil => intro B; rfl
  | cons t γ' ih =>
      intro B
      -- Same induction as `msubstAt_substAt_comm`; the per-element law is
      -- `substAt_substAt` at (j, k) := (e, d), whose placed value
      -- `substAt X t (d - e)` collapses to `X` by closedness.
      simp only [msubstAt]
      rw [ih (substAt B t (d + 1)),
          substAt_substAt X t B e d hed,
          substAt_closed hX t (d - e)]

/-! ### Closing an open term with a full environment -/

private theorem msubstAt_closes_gen :
    ∀ (γ : List Term), ClosedEnv γ → ∀ (M : Term) (d : Nat),
      ClosedAbove M (γ.length + d) → ClosedAbove (msubstAt M γ d) d := by
  intro γ
  induction γ with
  | nil =>
      intro _ M d hM
      simp only [msubstAt]
      simpa using hM
  | cons t γ' ih =>
      intro henv M d hM
      have ht : Closed t := henv t List.mem_cons_self
      have hM' : ClosedAbove M (γ'.length + d + 1) := by
        intro i hi
        apply hM i
        simp only [List.length_cons]
        omega
      simp only [msubstAt]
      exact ih (fun s hs => henv s (List.mem_cons_of_mem t hs)) (substAt M t d) d
        (substAt_closes_gen ht M (γ'.length + d) d hM' (by omega))

/-- `msubst` of a sufficiently-closed-above term under a full closed
environment is closed. -/
theorem msubst_closes {M : Term} {γ : List Term} (henv : ClosedEnv γ)
    (hM : ClosedAbove M γ.length) : Closed (msubst M γ) :=
  msubstAt_closes_gen γ henv M 0 (by simpa using hM)

/-! ## Free-variable bound from typing + related environments -/

/-- Well-typed terms use only variables below the context length. -/
theorem propDeriv_fvar_bound {Γₐ : List Prop'} {M : Term} {φ : Prop'}
    (d : PropDeriv Γₐ M φ) : ClosedAbove M Γₐ.length := by
  induction d with
  | varA Γ i χ h =>
      refine closedAbove_var_iff.mpr ?_
      by_contra hnot
      rw [List.getElem?_eq_none (by omega)] at h
      cases h
  | impI Γ χ ψ M' _ ih =>
      exact closedAbove_lam_iff.mpr
        (fun i hi => ih i (by simp only [List.length_cons]; omega))
  | impE Γ χ ψ M' N _ _ ihM ihN =>
      exact closedAbove_app_iff.mpr ⟨ihM, ihN⟩
  | saysI Γ p χ M' sig _ ih =>
      exact closedAbove_sign_iff.mpr ih
  | verifyE Γ p χ M' sig _ ih =>
      exact closedAbove_verify_iff.mpr ih
  | andI Γ χ ψ a b _ _ ihA ihB =>
      exact closedAbove_pair_iff.mpr ⟨ihA, ihB⟩
  | andEL Γ χ ψ a _ ih =>
      exact closedAbove_fst_iff.mpr ih
  | andER Γ χ ψ a _ ih =>
      exact closedAbove_snd_iff.mpr ih
  | withinI Γ τ χ M' _ ih =>
      exact closedAbove_withinIntro_iff.mpr ih
  | orI_L Γ χ ψ a _ ih =>
      exact closedAbove_inl_iff.mpr ih
  | orI_R Γ χ ψ a _ ih =>
      exact closedAbove_inr_iff.mpr ih
  | tensorI Γ χ ψ a b _ _ ihA ihB =>
      exact closedAbove_tensorIntro_iff.mpr ⟨ihA, ihB⟩
  | orE Γ χ ψ ρ S L R _ _ _ ihS ihL ihR =>
      exact closedAbove_case_iff.mpr
        ⟨ihS,
         fun i hi => ihL i (by simp only [List.length_cons]; omega),
         fun i hi => ihR i (by simp only [List.length_cons]; omega)⟩
  | letSaysE Γ p χ ψ S B _ _ ihS ihB =>
      exact closedAbove_letSays_iff.mpr
        ⟨ihS, fun i hi => ihB i (by simp only [List.length_cons]; omega)⟩
  | sfExtractE Γ p q M' _ ih =>
      exact closedAbove_sfExtract_iff.mpr ih
  | delegate Γ p q χ M' N _ _ ihM ihN =>
      exact closedAbove_delegate_iff.mpr ⟨ihM, ihN⟩
  | now Γ τ =>
      exact closedAbove_now
  | attenuate Γ p χ M' _ ih =>
      exact closedAbove_attenuate_iff.mpr ih
  | liftLabel Γ χ ℓ M' _ ih =>
      exact closedAbove_liftLabel_iff.mpr ih
  | declassify Γ χ ℓ ℓ' M' π _ _ ihM ihπ =>
      exact closedAbove_declassify_iff.mpr ⟨ihM, ihπ⟩
  | discharge Γ O χ M' N _ _ ihM ihN =>
      exact closedAbove_discharge_iff.mpr ⟨ihM, ihN⟩
  | letTensor Γ χ ψ ρ S B _ _ ihS ihB =>
      exact closedAbove_letTensor_iff.mpr
        ⟨ihS, fun i hi => ihB i (by simp only [List.length_cons]; omega)⟩
  | commitI Γ issuer capProp φ ℓ M c _ _ ihc ihM =>
      exact closedAbove_command_iff.mpr ⟨ihM, ihc⟩

/-- Pointwise `LRel`-related, closed environments for a context. -/
inductive EnvRel (ℓLow : Label) : List Prop' → List Term → List Term → Prop where
  | nil : EnvRel ℓLow [] [] []
  | cons {φ : Prop'} {Γₐ : List Prop'} {t₁ t₂ : Term} {γ₁ γ₂ : List Term} :
      LRel ℓLow φ t₁ t₂ → Closed t₁ → Closed t₂ →
      EnvRel ℓLow Γₐ γ₁ γ₂ → EnvRel ℓLow (φ :: Γₐ) (t₁ :: γ₁) (t₂ :: γ₂)

theorem EnvRel.length_left {ℓLow : Label} {Γₐ : List Prop'} {γ₁ γ₂ : List Term}
    (h : EnvRel ℓLow Γₐ γ₁ γ₂) : γ₁.length = Γₐ.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [List.length_cons, ih]

theorem EnvRel.length_right {ℓLow : Label} {Γₐ : List Prop'} {γ₁ γ₂ : List Term}
    (h : EnvRel ℓLow Γₐ γ₁ γ₂) : γ₂.length = Γₐ.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [List.length_cons, ih]

theorem EnvRel.closed_left {ℓLow : Label} {Γₐ : List Prop'} {γ₁ γ₂ : List Term}
    (h : EnvRel ℓLow Γₐ γ₁ γ₂) : ClosedEnv γ₁ := by
  induction h with
  | nil => intro t ht; simp at ht
  | cons _ hc₁ _ _ ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hc₁
      · exact ih s hs'

theorem EnvRel.closed_right {ℓLow : Label} {Γₐ : List Prop'} {γ₁ γ₂ : List Term}
    (h : EnvRel ℓLow Γₐ γ₁ γ₂) : ClosedEnv γ₂ := by
  induction h with
  | nil => intro t ht; simp at ht
  | cons _ _ hc₂ _ ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hc₂
      · exact ih s hs'

/-- The var case of the fundamental lemma, packaged: a typed variable's two
substitution instances are related. -/
theorem EnvRel.lookup {ℓLow : Label} {Γₐ : List Prop'} {γ₁ γ₂ : List Term}
    (h : EnvRel ℓLow Γₐ γ₁ γ₂)
    {i : Nat} {φ : Prop'} (hslot : Γₐ[i]? = some φ) :
    LRel ℓLow φ (msubst (Term.var i) γ₁) (msubst (Term.var i) γ₂) := by
  induction h generalizing i with
  | nil => simp at hslot
  | cons hrel hc₁ hc₂ _ ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hslot
          subst hslot
          simp only [msubst, msubstAt, substAt_var_eq, shift_zero,
            msubstAt_closed hc₁, msubstAt_closed hc₂]
          exact hrel
      | succ i' =>
          simp only [List.getElem?_cons_succ] at hslot
          simp only [msubst, msubstAt, substAt_var_succ]
          exact ih hslot

end DLC
