/-
# `attenuate` only narrows — the offline-attenuation soundness metatheorem.

The DLC-D interop story (`spec/interop-says-biscuit.md` §1) maps `Term.Attenuate`
onto Biscuit's **offline attenuation**: a holder may append a block that *narrows*
the authority a token grants, never one that widens it. The Tamarin interop model
(`models/tamarin/dlcd-interop.spthy`, lemma `attenuation_roots_in_issuance`) assumes
this *structurally* — it is the one place the interop guarantee rested on an
assumption about the calculus rather than a proof about it (§2/§7 name it a gap).

This file discharges that assumption on `Deriv`. The `attenuate` rule
(`lean/DLC/Judgment.lean`) is

    attenuate (Γ p φ ψ M N) (d : Deriv Γ M (says p φ))
                            (impl : Deriv (consA φ empty) N ψ)
      : Deriv Γ (attenuate M ψ) (says p ψ)

so the attenuated authority `ψ` is only ever concluded when there is a derivation
`impl` of `ψ` from the parent authority's proposition `φ` in a singleton context —
i.e. `φ ⊢ ψ`. Entailment **is** the narrowing order (if `φ ⊢ ψ` then `ψ` grants no
more than `φ`; e.g. `a ∧ b ⊢ a`). The metatheorem is the *generation* (inversion)
lemma: from any well-typed `attenuate` node we can recover the parent authority
`p says φ` on the same subject AND the narrowing witness `φ ⊢ ψ`.

## Not vacuous

The statement deliberately ties `φ` to the parent's *actual* type
`Deriv Γ M (says p φ)`. The weaker `∃ φ, Deriv (consA φ empty) N ψ` would be
vacuous — take `φ := ψ`, `N := var 0` and `Deriv.varA` proves it for *every* `ψ`,
saying nothing about attenuation. `attenuate_narrows_genuinely` exhibits a concrete
*non-identity* narrowing (`p says (a ∧ b)` ↝ `p says a`) so the recovered `φ ≠ ψ`.

## Fences

- **Generation lemma, on `Deriv`.** This proves that a *typed* attenuate node carries
  the narrowing witness. It is not the converse (`ψ` genuinely underivable from `φ` ⟹
  no node): that is the Deriv-*consistency* direction (no widening is derivable), which
  needs a semantic model of `Deriv` and is the next increment.
- **Checker-level bite.** `decideLean_refuses_nonidentity_attenuation` shows the shipped
  checker (`decideLean`) returns `none` on a non-narrowing attenuation — a computable
  right-reason bite that the attenuation rule is not a rubber stamp. Honest gap:
  `decideLean`'s attenuate arm is *identity-only* (stricter than `Deriv`-narrowing, a
  known Lean/Rust fragment gap), so `none` over-approximates the block and does not by
  itself establish `Deriv`-level non-derivability.

Prior art (web, this increment): Biscuit offline attenuation = chained signed blocks,
each strictly narrowing (biscuit SPECIFICATIONS.md; biscuitsec.org); the
capability-monotonicity / subsumption invariant ("at least as restrictive as") —
eclipse-biscuit/biscuit `SPECIFICATIONS.md`, draft-niyikiza-oauth-attenuating-agent-tokens-00
(IETF), Macaroons→Biscuit asymmetric-signature attenuation.
-/
import DLC.Judgment
import DLC.Subst
import DLC.Decidability

namespace DLC

/-- Inversion of `shift` at an `attenuate` head: since `shift` recurses structurally
and leaves the `ψ` annotation untouched (`Subst.lean`, `attenuate` arm), a shifted
term can only *be* an `attenuate M ψ` if it was one before the shift. -/
theorem shift_eq_attenuate :
    ∀ {t : Term} {δ c : Nat} {m : Term} {ψ : Prop'},
      shift t δ c = Term.attenuate m ψ →
      ∃ m₀, t = Term.attenuate m₀ ψ ∧ shift m₀ δ c = m := by
  intro t δ c m ψ h
  cases t with
  | attenuate m₀ ψ₀ =>
    simp only [shift] at h
    injection h with h1 h2
    subst h2
    exact ⟨m₀, rfl, h1⟩
  | var i =>
    simp only [shift] at h
    split at h <;> simp at h
  | _ => simp [shift] at h

/-- **Generation lemma (auxiliary).** Any derivation whose subject is `attenuate M ψ`
carries (i) that its conclusion is `says p ψ` for some `p`, (ii) the parent authority
`M : says p φ`, and (iii) the narrowing witness `φ ⊢ ψ`. The conclusion `C` is left
general so the two subject-preserving rules invert cleanly: `weakenA` (shifted subject)
re-weakens the recovered parent; `withinE` (bare subject, conclusion stripped of a
`within`) is impossible — its premise conclusion would have to be both `within τ _` and,
by the IH, `says _ ψ`, a constructor clash. Every other constructor has a distinct
subject head. Returning the says-shape (i) is what makes the `withinE` case dischargeable
and keeps the statement non-vacuous (the parent's `φ` is tied to `M`'s real type). -/
theorem attenuate_narrows_aux :
    ∀ {Γ : Ctx} {S : Term} {C : Prop'}, Deriv Γ S C →
      ∀ {ψ : Prop'} {M : Term}, S = Term.attenuate M ψ →
        ∃ (p : Principal) (φ : Prop') (N : Term),
          C = Prop'.says p ψ ∧
          Nonempty (Deriv Γ M (Prop'.says p φ)) ∧
          Nonempty (Deriv (Ctx.consA φ Ctx.empty) N ψ) := by
  intro Γ S C d
  induction d with
  | attenuate Γ' p' φ' ψ' M' N' dp impl _ _ =>
    intro ψ M hS
    injection hS with hM hψ
    subst hM; subst hψ
    exact ⟨p', φ', N', rfl, ⟨dp⟩, ⟨impl⟩⟩
  | weakenA Γ'' φ'' _φ_ty M'' _ ih =>
    intro ψ M hS
    obtain ⟨m₀, hM''eq, hshift⟩ := shift_eq_attenuate hS
    obtain ⟨p, φ_par, N_w, hCeq, ⟨dp'⟩, hw_impl⟩ := ih hM''eq
    refine ⟨p, φ_par, N_w, hCeq, ?_, hw_impl⟩
    have hw := Deriv.weakenA Γ'' φ'' (Prop'.says p φ_par) m₀ dp'
    rw [hshift] at hw
    exact ⟨hw⟩
  | withinE Γ_w τ φ_w M_w _ ih =>
    intro ψ M hS
    obtain ⟨_, _, _, hCeq, _, _⟩ := ih hS
    exact absurd hCeq (by simp)
  | _ =>
    intro ψ M hS
    contradiction

/-- **`attenuate` only narrows.** From a well-typed attenuation
`Γ ⊢ attenuate M ψ : p says ψ`, recover (a) the parent authority `Γ ⊢ M : p says φ`
on the *same* subject `M`, and (b) a derivation of `ψ` from `φ` (the narrowing
witness `φ ⊢ ψ`). The attenuated authority is thus always a logical consequence of —
never wider than — the parent authority. -/
theorem attenuate_only_narrows
    {Γ : Ctx} {p : Principal} {ψ : Prop'} {M : Term}
    (d : Deriv Γ (Term.attenuate M ψ) (Prop'.says p ψ)) :
    ∃ (φ : Prop') (N : Term),
      Nonempty (Deriv Γ M (Prop'.says p φ)) ∧
      Nonempty (Deriv (Ctx.consA φ Ctx.empty) N ψ) := by
  obtain ⟨p', φ, N, hCeq, hpar, hwit⟩ := attenuate_narrows_aux d rfl
  injection hCeq with hp _
  subst hp
  exact ⟨φ, N, hpar, hwit⟩

/-- **Anti-vacuity witness (a genuine, non-identity narrowing).** `p says (a ∧ b)`
attenuated to `p says a`: the recovered parent proposition `a ∧ b` is strictly larger
than the conclusion `a`, so `attenuate_only_narrows` is not the vacuous `φ := ψ`
degenerate case. `andEL` supplies the narrowing witness `a ∧ b ⊢ a`. A real derivation
term (not `Nonempty`), so it is a concrete inhabitant. -/
def attenuate_narrows_genuinely (p : Principal) :
    Deriv
      (Ctx.consA (Prop'.says p (Prop'.and (Prop'.atom 0) (Prop'.atom 1))) Ctx.empty)
      (Term.attenuate (Term.var 0) (Prop'.atom 0))
      (Prop'.says p (Prop'.atom 0)) :=
  Deriv.attenuate _ p (Prop'.and (Prop'.atom 0) (Prop'.atom 1)) (Prop'.atom 0)
    (Term.var 0) (Term.fst (Term.var 0))
    (Deriv.varA _ 0 _ rfl)
    (Deriv.andEL _ (Prop'.atom 0) (Prop'.atom 1) (Term.var 0) (Deriv.varA _ 0 _ rfl))

/-- Running the generation lemma on the witness recovers a parent proposition — the
machine-checked demonstration that the recovered `φ` is the real parent authority
(`a ∧ b`), not the trivial `φ := ψ`. -/
theorem attenuate_narrows_genuinely_recovers_parent (p : Principal) :
    ∃ (φ : Prop') (N : Term),
      Nonempty (Deriv
        (Ctx.consA (Prop'.says p (Prop'.and (Prop'.atom 0) (Prop'.atom 1))) Ctx.empty)
        (Term.var 0) (Prop'.says p φ)) ∧
      Nonempty (Deriv (Ctx.consA φ Ctx.empty) N (Prop'.atom 0)) :=
  attenuate_only_narrows (attenuate_narrows_genuinely p)

/-- **Checker-level right-reason bite (computable, axiom-clean via `decide`).** The
shipped checker `decideLean` REFUSES to attenuate `p says (atom 0)` to `p says (atom 1)`:
the annotation is not a free-floating claim the checker rubber-stamps. Perturbing `ψ`
to a non-narrowing value turns the accept into a `none`. (Fence: `decideLean`'s
attenuate arm is identity-only, stricter than `Deriv`-narrowing, so this blocks the
widening a fortiori.) A concrete principal is used so the goal is closed. -/
theorem decideLean_refuses_nonidentity_attenuation :
    decideLean
      (Ctx.consA (Prop'.says (Principal.atom ⟨[]⟩) (Prop'.atom 0)) Ctx.empty)
      (Term.attenuate (Term.var 0) (Prop'.atom 1)) = none := by
  rfl

/-- Companion accept: the identity narrowing IS accepted, so the `none` above is a real
discrimination (the checker accepts something at this subject), not a blanket refusal. -/
theorem decideLean_accepts_identity_attenuation :
    decideLean
      (Ctx.consA (Prop'.says (Principal.atom ⟨[]⟩) (Prop'.atom 0)) Ctx.empty)
      (Term.attenuate (Term.var 0) (Prop'.atom 0))
        = some (Prop'.says (Principal.atom ⟨[]⟩) (Prop'.atom 0)) := by
  rfl

/-!
## Chaining — narrowing composes over a multi-hop attenuation chain.

Biscuit's authority is attenuated by *appending* blocks, each strictly narrowing; the security
property (Tamarin `attenuation_roots_in_issuance`, generalized to N blocks) is that the LEAF
authority a chain grants is still entailed by the ROOT the issuer signed. In Garg–Pfenning
constructive authorization logic this is the transitivity of entailment that underwrites cut
admissibility ([csfw06]; [affknow06]). Here the narrowing order is `φ ⊢ ψ` (a `Deriv` in the
singleton additive context), so chaining is exactly transitivity of that relation.
-/

/-- **Entailment is transitive (the singleton-context cut).** From `φ ⊢ ψ` and `ψ ⊢ χ` build
`φ ⊢ χ`, WITHOUT a general substitution lemma: `impI` internalizes `ψ ⊢ χ` as `⊢ ψ ⊃ χ`, `weakenA`
moves it under the `φ` hypothesis, and `impE` applies it to the `φ ⊢ ψ` derivation. The composed
subject term is immaterial (existential), so `impE`'s argument-shift is harmless. -/
theorem entail_trans {φ ψ χ : Prop'} {N N' : Term}
    (d1 : Deriv (Ctx.consA φ Ctx.empty) N ψ)
    (d2 : Deriv (Ctx.consA ψ Ctx.empty) N' χ) :
    ∃ (Nc : Term), Nonempty (Deriv (Ctx.consA φ Ctx.empty) Nc χ) := by
  have himp : Deriv Ctx.empty (Term.lam ψ N') (Prop'.imp ψ χ) :=
    Deriv.impI Ctx.empty ψ χ N' d2
  have himpW : Deriv (Ctx.consA φ Ctx.empty) (shift (Term.lam ψ N') 1 0) (Prop'.imp ψ χ) :=
    Deriv.weakenA Ctx.empty φ (Prop'.imp ψ χ) (Term.lam ψ N') himp
  exact ⟨_, ⟨Deriv.impE [φ] [] [] ψ χ (shift (Term.lam ψ N') 1 0) N himpW d1⟩⟩

/-- **`attenuate` chaining — the leaf authority is entailed by the root.** For a two-hop chain
`attenuate (attenuate M ψ₁) ψ₂ : p says ψ₂`, recover the ROOT authority `M : p says φ_root` and a
derivation `φ_root ⊢ ψ₂`: the leaf `ψ₂` is a logical consequence of the root the issuer signed,
across the whole chain (not merely of the immediately preceding hop). By induction this extends to
N hops; the two-hop case is the inductive step (`attenuate_only_narrows` twice, then `entail_trans`).
The inner application uses the auxiliary generation lemma to learn the middle hop's says-shape
(`φ_a = ψ₁`) before composing. -/
theorem attenuate_chain_narrows
    {Γ : Ctx} {p : Principal} {ψ₁ ψ₂ : Prop'} {M : Term}
    (d : Deriv Γ (Term.attenuate (Term.attenuate M ψ₁) ψ₂) (Prop'.says p ψ₂)) :
    ∃ (φ_root : Prop') (N : Term),
      Nonempty (Deriv Γ M (Prop'.says p φ_root)) ∧
      Nonempty (Deriv (Ctx.consA φ_root Ctx.empty) N ψ₂) := by
  obtain ⟨_φ_a, _N_a, ⟨dOuterParent⟩, ⟨dLeafNarrow⟩⟩ := attenuate_only_narrows d
  obtain ⟨p'', φ_b, _N_b, hCeq, ⟨dRoot⟩, ⟨dMidNarrow⟩⟩ := attenuate_narrows_aux dOuterParent rfl
  injection hCeq with hp hφa
  subst hφa
  subst hp
  obtain ⟨Nc, dTrans⟩ := entail_trans dMidNarrow dLeafNarrow
  exact ⟨φ_b, Nc, ⟨dRoot⟩, dTrans⟩

/-- **Anti-vacuity witness — a genuine two-hop chain.** Root `p says (a₀ ∧ (a₁ ∧ a₂))`, narrowed to
`p says (a₁ ∧ a₂)` (via `andER`), then to `p says a₁` (via `andEL`). Every hop is a real, non-identity
narrowing, so `attenuate_chain_narrows` is exercised on a genuinely multi-hop chain — its recovered
root `a₀ ∧ (a₁ ∧ a₂)` is strictly larger than both the mid `a₁ ∧ a₂` and the leaf `a₁`. -/
def attenuate_chain_witness (p : Principal) :
    Deriv
      (Ctx.consA (Prop'.says p
        (Prop'.and (Prop'.atom 0) (Prop'.and (Prop'.atom 1) (Prop'.atom 2)))) Ctx.empty)
      (Term.attenuate
        (Term.attenuate (Term.var 0) (Prop'.and (Prop'.atom 1) (Prop'.atom 2)))
        (Prop'.atom 1))
      (Prop'.says p (Prop'.atom 1)) :=
  Deriv.attenuate _ p (Prop'.and (Prop'.atom 1) (Prop'.atom 2)) (Prop'.atom 1)
    (Term.attenuate (Term.var 0) (Prop'.and (Prop'.atom 1) (Prop'.atom 2)))
    (Term.fst (Term.var 0))
    (Deriv.attenuate _ p
      (Prop'.and (Prop'.atom 0) (Prop'.and (Prop'.atom 1) (Prop'.atom 2)))
      (Prop'.and (Prop'.atom 1) (Prop'.atom 2)) (Term.var 0) (Term.snd (Term.var 0))
      (Deriv.varA _ 0 _ rfl)
      (Deriv.andER _ (Prop'.atom 0) (Prop'.and (Prop'.atom 1) (Prop'.atom 2))
        (Term.var 0) (Deriv.varA _ 0 _ rfl)))
    (Deriv.andEL _ (Prop'.atom 1) (Prop'.atom 2) (Term.var 0) (Deriv.varA _ 0 _ rfl))

/-- The chaining theorem, applied to the genuine two-hop witness: the leaf `a₁` is recovered as
entailed by the root `a₀ ∧ (a₁ ∧ a₂)` — non-vacuously (the recovered root ≠ the leaf). -/
theorem attenuate_chain_narrows_witness (p : Principal) :
    ∃ (φ_root : Prop') (N : Term),
      Nonempty (Deriv (Ctx.consA (Prop'.says p
          (Prop'.and (Prop'.atom 0) (Prop'.and (Prop'.atom 1) (Prop'.atom 2)))) Ctx.empty)
        (Term.var 0) (Prop'.says p φ_root)) ∧
      Nonempty (Deriv (Ctx.consA φ_root Ctx.empty) N (Prop'.atom 1)) :=
  attenuate_chain_narrows (attenuate_chain_witness p)

end DLC
