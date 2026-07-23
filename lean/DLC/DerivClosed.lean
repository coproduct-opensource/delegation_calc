import DLC.Judgment
import DLC.NonInterferenceEnv

/-! # Every derivable term is closed above its context size

`deriv_closedAbove` : if `Γ ⊢ M : φ` then `M` has no free de Bruijn index at
or above `Γ.additive.length + Γ.linear.length`. In particular a derivation in
`Ctx.empty` yields a `Closed` term.

This is the missing lemma for **L3a's `boxI` case**: `boxI`'s obligation
premise `dN : Deriv Ctx.empty N (Prop'.atom 0)` sits in a FIXED context while
the conclusion term `Term.boxed O M N` is shifted, and `N` carries no
induction hypothesis. `deriv_closedAbove` gives `Closed N`, and then
`shift_closed` makes the shift on `N` a no-op. The statement is
representation-independent: under any context representation, `boxI`'s
fixed-context premise still needs its term closed.

`Deriv` is `Type`-valued, so the eliminations are `noncomputable def`s that
return the `Prop` `ClosedAbove …`.
-/

namespace DLC

open Term Prop'

/-- Closedness bound is upward monotone: fewer free indices is preserved by
raising the threshold. -/
theorem closedAbove_mono {t : Term} {k k' : Nat}
    (h : ClosedAbove t k) (hk : k ≤ k') : ClosedAbove t k' :=
  fun i hi => h i (Nat.le_trans hk hi)

/-- **Shift raises the closedness bound.** If `t` has no free index at or
above `k`, then `shift t d c` has none at or above `k + d`. Holds for every
cutoff `c`: indices below `c` are unmoved (and stay `< k ≤ k + d`), indices
at or above `c` gain `d` (and were `< k`, so land `< k + d`). -/
theorem closedAbove_shift :
    ∀ (t : Term) (k d c : Nat), ClosedAbove t k → ClosedAbove (shift t d c) (k + d) := by
  intro t
  induction t with
  | var j =>
      intro k d c h
      rw [closedAbove_var_iff] at h
      simp only [shift]
      by_cases hjc : j < c
      · rw [if_pos hjc, closedAbove_var_iff]; omega
      · rw [if_neg hjc, closedAbove_var_iff]; omega
  | lam φ b ih =>
      intro k d c h
      rw [closedAbove_lam_iff] at h
      simp only [shift]
      rw [closedAbove_lam_iff, show k + d + 1 = (k + 1) + d from by omega]
      exact ih (k + 1) d (c + 1) h
  | app f x ihf ihx =>
      intro k d c h
      rw [closedAbove_app_iff] at h
      simp only [shift]
      rw [closedAbove_app_iff]
      exact ⟨ihf k d c h.1, ihx k d c h.2⟩
  | sign p m sig ih =>
      intro k d c h
      rw [closedAbove_sign_iff] at h
      simp only [shift]
      rw [closedAbove_sign_iff]; exact ih k d c h
  | verify p m sig ih =>
      intro k d c h
      rw [closedAbove_verify_iff] at h
      simp only [shift]
      rw [closedAbove_verify_iff]; exact ih k d c h
  | delegate m n ihm ihn =>
      intro k d c h
      rw [closedAbove_delegate_iff] at h
      simp only [shift]
      rw [closedAbove_delegate_iff]; exact ⟨ihm k d c h.1, ihn k d c h.2⟩
  | attenuate m ψ ih =>
      intro k d c h
      rw [closedAbove_attenuate_iff] at h
      simp only [shift]
      rw [closedAbove_attenuate_iff]; exact ih k d c h
  | boxed O m n ihm ihn =>
      intro k d c h
      rw [closedAbove_boxed_iff] at h
      simp only [shift]
      rw [closedAbove_boxed_iff]; exact ⟨ihm k d c h.1, ihn k d c h.2⟩
  | discharge m n ihm ihn =>
      intro k d c h
      rw [closedAbove_discharge_iff] at h
      simp only [shift]
      rw [closedAbove_discharge_iff]; exact ⟨ihm k d c h.1, ihn k d c h.2⟩
  | liftLabel ℓ m ih =>
      intro k d c h
      rw [closedAbove_liftLabel_iff] at h
      simp only [shift]
      rw [closedAbove_liftLabel_iff]; exact ih k d c h
  | declassify ℓ m π ihm ihπ =>
      intro k d c h
      rw [closedAbove_declassify_iff] at h
      simp only [shift]
      rw [closedAbove_declassify_iff]; exact ⟨ihm k d c h.1, ihπ k d c h.2⟩
  | now τ =>
      intro k d c _
      simp only [shift]
      intro i _; rfl
  | withinIntro τ m ih =>
      intro k d c h
      rw [closedAbove_withinIntro_iff] at h
      simp only [shift]
      rw [closedAbove_withinIntro_iff]; exact ih k d c h
  | pair a b iha ihb =>
      intro k d c h
      rw [closedAbove_pair_iff] at h
      simp only [shift]
      rw [closedAbove_pair_iff]; exact ⟨iha k d c h.1, ihb k d c h.2⟩
  | fst a ih =>
      intro k d c h
      rw [closedAbove_fst_iff] at h
      simp only [shift]
      rw [closedAbove_fst_iff]; exact ih k d c h
  | snd a ih =>
      intro k d c h
      rw [closedAbove_snd_iff] at h
      simp only [shift]
      rw [closedAbove_snd_iff]; exact ih k d c h
  | inl ψ a ih =>
      intro k d c h
      rw [closedAbove_inl_iff] at h
      simp only [shift]
      rw [closedAbove_inl_iff]; exact ih k d c h
  | inr φ a ih =>
      intro k d c h
      rw [closedAbove_inr_iff] at h
      simp only [shift]
      rw [closedAbove_inr_iff]; exact ih k d c h
  | case s l r ihs ihl ihr =>
      intro k d c h
      rw [closedAbove_case_iff] at h
      simp only [shift]
      rw [closedAbove_case_iff, show k + d + 1 = (k + 1) + d from by omega]
      exact ⟨ihs k d c h.1, ihl (k + 1) d (c + 1) h.2.1, ihr (k + 1) d (c + 1) h.2.2⟩
  | tensorIntro a b iha ihb =>
      intro k d c h
      rw [closedAbove_tensorIntro_iff] at h
      simp only [shift]
      rw [closedAbove_tensorIntro_iff]; exact ⟨iha k d c h.1, ihb k d c h.2⟩
  | letTensor s b ihs ihb =>
      intro k d c h
      rw [closedAbove_letTensor_iff] at h
      simp only [shift]
      rw [closedAbove_letTensor_iff, show k + d + 2 = (k + 2) + d from by omega]
      exact ⟨ihs k d c h.1, ihb (k + 2) d (c + 2) h.2⟩
  | saysBind p s b ihs ihb =>
      intro k d c h
      rw [closedAbove_saysBind_iff] at h
      simp only [shift]
      rw [closedAbove_saysBind_iff, show k + d + 1 = (k + 1) + d from by omega]
      exact ⟨ihs k d c h.1, ihb (k + 1) d (c + 1) h.2⟩
  | letSays p s b ihs ihb =>
      intro k d c h
      rw [closedAbove_letSays_iff] at h
      simp only [shift]
      rw [closedAbove_letSays_iff, show k + d + 1 = (k + 1) + d from by omega]
      exact ⟨ihs k d c h.1, ihb (k + 1) d (c + 1) h.2⟩
  | sfExtract m ih =>
      intro k d c h
      rw [closedAbove_sfExtract_iff] at h
      simp only [shift]
      rw [closedAbove_sfExtract_iff]; exact ih k d c h
  | command m cr ℓ ihm ihcr =>
      intro k d c h
      rw [closedAbove_command_iff] at h
      simp only [shift]
      rw [closedAbove_command_iff]
      exact ⟨ihm k d c h.1, ihcr k d c h.2⟩
  | runCmd v s ihv ihs =>
      intro k d c h
      rw [closedAbove_runCmd_iff] at h
      simp only [shift]
      rw [closedAbove_runCmd_iff]
      exact ⟨ihv k d c h.1, ihs k d c h.2⟩

/-- Convenience: the additive-and-linear size of a context. -/
def Ctx.size (Γ : Ctx) : Nat := Γ.additive.length + Γ.linear.length

/-- **L3a boxI prerequisite.** Every derivable term is closed above its
context size. `Deriv` is `Type`-valued, so this is a `noncomputable def`
into the proposition `ClosedAbove M Γ.size`. -/
noncomputable def deriv_closedAbove {Γ : Ctx} {M : Term} {φ : Prop'}
    (d : Deriv Γ M φ) : ClosedAbove M Γ.size := by
  induction d with
  | varA Γ i χ h =>
      rw [closedAbove_var_iff]
      have hlt : i < Γ.additive.length := by
        by_contra hge
        rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hge)] at h
        exact absurd h.symm (Option.some_ne_none χ)
      simp only [Ctx.size]; omega
  | varL Γₐ χ =>
      rw [closedAbove_var_iff]; simp only [Ctx.size]; simp
  | weakenA Γ φ' χ N _d ih =>
      have h := closedAbove_shift N Γ.size 1 0 ih
      simpa [Ctx.size, Ctx.consA, Nat.add_right_comm] using h
  | impI Γ χ ψ N _d ih =>
      rw [closedAbove_lam_iff]
      simpa [Ctx.size, Ctx.consA, Nat.add_right_comm] using ih
  | impE Γₐ Γ₁ Γ₂ χ ψ A B _dM _dN ihM ihN =>
      rw [closedAbove_app_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihM) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + Γ₂.length) Γ₁.length Γₐ.length
                  (by simpa [Ctx.size] using ihN)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | saysI Γ p χ N sig _d ih =>
      rw [closedAbove_sign_iff]; simpa [Ctx.size] using ih
  | verifyE Γ p χ N sig _d ih =>
      rw [closedAbove_verify_iff]; simpa [Ctx.size] using ih
  | saysE Γₐ Γ₁ Γ₂ p χ ψ A B _dM _dN ihM ihN =>
      rw [closedAbove_saysBind_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihM) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + 1 + Γ₂.length) Γ₁.length (Γₐ.length + 1)
                  (by simpa [Ctx.size, Nat.add_right_comm] using ihN)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | delegate Γₐ Γ₁ Γ₂ p q χ A B _dM _dN ihM ihN =>
      rw [closedAbove_delegate_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihM) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + Γ₂.length) Γ₁.length Γₐ.length
                  (by simpa [Ctx.size] using ihN)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | attenuate Γ p χ ψ A B _d impl ih _ihImpl =>
      rw [closedAbove_attenuate_iff]; simpa [Ctx.size] using ih
  | boxI Γ O χ A B _dM dN ihM _ihN =>
      rw [closedAbove_boxed_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihM) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      -- dN : Deriv Ctx.empty B (atom 0). The recursion gives ClosedAbove B 0,
      -- i.e. Closed B; weaken the bound up to Γ.size.
      have hClosed : ClosedAbove B (Ctx.empty).size := _ihN
      have : ClosedAbove B 0 := by simpa [Ctx.size, Ctx.empty] using hClosed
      intro i _; exact this i (Nat.zero_le _)
  | discharge Γₐ Γ₁ Γ₂ O χ A B _dM _dN ihM ihN =>
      rw [closedAbove_discharge_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihM) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + Γ₂.length) Γ₁.length Γₐ.length
                  (by simpa [Ctx.size] using ihN)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | now Γₐ τ =>
      intro i _; rfl
  | withinI Γ τ χ N _d ih =>
      rw [closedAbove_withinIntro_iff]; simpa [Ctx.size] using ih
  | withinE Γ τ χ N _d ih =>
      simpa [Ctx.size] using ih
  | liftLabel Γ χ ℓ N _d ih =>
      rw [closedAbove_liftLabel_iff]; simpa [Ctx.size] using ih
  | declassify Γ χ ℓ ℓ' N π _d _dπ ih ihπ =>
      rw [closedAbove_declassify_iff]
      exact ⟨by simpa [Ctx.size] using ih, by simpa [Ctx.size] using ihπ⟩
  | andI Γₐ χ ψ A B _dM _dN ihM ihN =>
      rw [closedAbove_pair_iff]
      exact ⟨by simpa [Ctx.size] using ihM, by simpa [Ctx.size] using ihN⟩
  | andEL Γ χ ψ N _d ih =>
      rw [closedAbove_fst_iff]; simpa [Ctx.size] using ih
  | andER Γ χ ψ N _d ih =>
      rw [closedAbove_snd_iff]; simpa [Ctx.size] using ih
  | orI_L Γ χ ψ N _d ih =>
      rw [closedAbove_inl_iff]; simpa [Ctx.size] using ih
  | orI_R Γ χ ψ N _d ih =>
      rw [closedAbove_inr_iff]; simpa [Ctx.size] using ih
  | orE Γₐ χ ψ ξ S L R _dS _dL _dR ihS ihL ihR =>
      rw [closedAbove_case_iff]
      refine ⟨by simpa [Ctx.size] using ihS, ?_, ?_⟩
      · simpa [Ctx.size, Nat.add_right_comm] using ihL
      · simpa [Ctx.size, Nat.add_right_comm] using ihR
  | tensorI Γₐ Γ₁ Γ₂ χ ψ A B _dM _dN ihM ihN =>
      rw [closedAbove_tensorIntro_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihM) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + Γ₂.length) Γ₁.length Γₐ.length
                  (by simpa [Ctx.size] using ihN)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | tensorE Γₐ Γ₁ Γ₂ χ ψ ξ S B _dS _dB ihS ihB =>
      rw [closedAbove_letTensor_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihS) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + 2 + Γ₂.length) Γ₁.length (Γₐ.length + 2)
                  (by simpa [Ctx.size, Nat.add_right_comm, Nat.add_assoc] using ihB)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | letTensorA Γₐ χ ψ ξ S B _dS _dB ihS ihB =>
      rw [closedAbove_letTensor_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihS) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      simpa [Ctx.size, Nat.add_right_comm] using ihB
  | letSaysE Γₐ Γ₁ Γ₂ p χ ψ S B _dS _dB ihS ihB =>
      rw [closedAbove_letSays_iff]
      refine ⟨closedAbove_mono (by simpa [Ctx.size] using ihS) (by simp only [Ctx.size, List.length_append]; omega), ?_⟩
      have h := closedAbove_shift B (Γₐ.length + 1 + Γ₂.length) Γ₁.length (Γₐ.length + 1)
                  (by simpa [Ctx.size, Nat.add_right_comm] using ihB)
      simpa [Ctx.size, List.length_append, Nat.add_right_comm, Nat.add_assoc,
             Nat.add_left_comm] using h
  | sfExtractE Γ p q N _d ih =>
      rw [closedAbove_sfExtract_iff]; simpa [Ctx.size] using ih
  | commitI Γₐ issuer capProp φ ℓ M cr dc dM ihdc ihdM =>
      rw [closedAbove_command_iff]
      exact ⟨ihdM, ihdc⟩
  | runCmd Γₐ φ ℓ V s dV ds ihdV ihds =>
      rw [closedAbove_runCmd_iff]
      exact ⟨ihdV, ihds⟩

/-- A derivation in the empty context yields a closed term. This is the exact
shape `boxI`'s obligation premise needs to make its conclusion-shift a no-op
via `shift_closed`. -/
noncomputable def deriv_closed_of_empty {M : Term} {φ : Prop'}
    (d : Deriv Ctx.empty M φ) : Closed M := by
  have h := deriv_closedAbove d
  simpa [Ctx.size, Ctx.empty, Closed] using h

end DLC

#print axioms DLC.deriv_closedAbove
#print axioms DLC.deriv_closed_of_empty
