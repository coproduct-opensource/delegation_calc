/-
T1 — Decidability of proof-checking.

The headline statement (to be closed at M1.Q2.d):

  ∀ Γ M φ, Decidable (Nonempty (Deriv Γ M φ))

with the complexity bound

  time(decide_pure Γ M φ) ≤ c · |M| · log |Γ|

The Q2 milestone closes T1 for the **propositional fragment** (no `◇_τ`,
no `□_O`, no IFC labels, no linear connectives). The full-calculus closure
is M1.Q4.d.

This file closes the **soundness direction** of T1 for the propositional
fragment: `decideLean Γ M = some φ → Nonempty (Deriv Γ M φ)`. The
completeness direction (`Nonempty (Deriv Γ M φ) → decideLean Γ M = some φ`)
is the next sub-PR; together they yield the `Decidable (Nonempty (Deriv …))`
instance the headline statement requires.

`decideLean` mirrors `crates/dlc-core/src/decide.rs::infer` restricted to
the propositional fragment (`Var`, `Lam`, `App`, `Sign`). All non-
propositional constructors return `none` — the checker is total on the
calculus but only meaningful on the fragment.

Per CLAUDE.md we do not introduce `sorry`. The completeness direction is
stated as a `def` returning `Prop`; closed in a follow-up PR.
-/

import DLC.Judgment
import DLC.Reduce

namespace DLC

/-- A propositional-fragment term has no modal (beyond `says`),
temporal, IFC, or linear constructors. Includes `var`, `lam`, `app`,
`sign` (says-I), and `verify` (says-E). -/
def Term.isPropositional : Term → Bool
  | Term.var _            => true
  | Term.lam _ body       => body.isPropositional
  | Term.app f x          => f.isPropositional && x.isPropositional
  | Term.sign _ m _       => m.isPropositional
  | Term.verify _ m _     => m.isPropositional
  | Term.pair a b         => a.isPropositional && b.isPropositional
  | Term.fst a            => a.isPropositional
  | Term.snd a            => a.isPropositional
  | Term.withinIntro _ m  => m.isPropositional
  | Term.inl _ a          => a.isPropositional
  | Term.inr _ a          => a.isPropositional
  | Term.tensorIntro a b  => a.isPropositional && b.isPropositional
  | Term.case s l r       => s.isPropositional && l.isPropositional && r.isPropositional
  | Term.letSays _ s b    => s.isPropositional && b.isPropositional
  | Term.sfExtract m      => m.isPropositional
  | Term.delegate m n     => m.isPropositional && n.isPropositional
  | Term.now _            => true
  | Term.attenuate m _    => m.isPropositional
  | Term.liftLabel _ m    => m.isPropositional
  | Term.declassify _ m π => m.isPropositional && π.isPropositional
  | Term.boxed _ m n      => m.isPropositional && n.isPropositional
  | Term.discharge m n    => m.isPropositional && n.isPropositional
  | Term.letTensor s b    => s.isPropositional && b.isPropositional

/-- A full-calculus term: every constructor accepted, including modal /
temporal / IFC / linear forms. The Q4 `decide_pure` (Rust mirror at
`crates/dlc-core/src/decide.rs::infer`) accepts this entire grammar. -/
def Term.isInCalculus : Term → Bool
  | Term.var _              => true
  | Term.lam _ body         => body.isInCalculus
  | Term.app f x            => f.isInCalculus && x.isInCalculus
  | Term.sign _ m _         => m.isInCalculus
  | Term.verify _ m _       => m.isInCalculus
  | Term.delegate m n       => m.isInCalculus && n.isInCalculus
  | Term.attenuate m _      => m.isInCalculus
  | Term.boxed _ m n        => m.isInCalculus && n.isInCalculus
  | Term.discharge m n      => m.isInCalculus && n.isInCalculus
  | Term.liftLabel _ m      => m.isInCalculus
  | Term.declassify _ m π   => m.isInCalculus && π.isInCalculus
  | Term.now _              => true
  | Term.withinIntro _ m    => m.isInCalculus
  | Term.pair a b           => a.isInCalculus && b.isInCalculus
  | Term.fst a              => a.isInCalculus
  | Term.snd a              => a.isInCalculus
  | Term.inl _ a            => a.isInCalculus
  | Term.inr _ a            => a.isInCalculus
  | Term.case s l r         => s.isInCalculus && l.isInCalculus && r.isInCalculus
  | Term.tensorIntro a b    => a.isInCalculus && b.isInCalculus
  | Term.letTensor s b      => s.isInCalculus && b.isInCalculus
  | Term.letSays _ s b      => s.isInCalculus && b.isInCalculus
  | Term.sfExtract m        => m.isInCalculus

/-! ## Decidable equality on `Prop'`.

`Prop'` carries `Label` (alias for nucleus's `CapabilityLattice`); with
`DecidableEq` attached to `CapabilityLevel`/`CapabilityLattice` in
`DLC.IFCLabel`, `Prop'.beq` is now **structurally complete** on every
constructor, including `at`. The companion lemma
`Prop'.beq_eq_true_iff_eq` proves the iff direction; `Prop'.beq_refl`
proves reflexivity — both load-bearing for T1's `Decidable` instance. -/
def Prop'.beq : Prop' → Prop' → Bool
  | .top, .top => true
  | .bot, .bot => true
  | .atom n, .atom m => n == m
  | .imp a b, .imp a' b' => Prop'.beq a a' && Prop'.beq b b'
  | .and a b, .and a' b' => Prop'.beq a a' && Prop'.beq b b'
  | .or a b, .or a' b' => Prop'.beq a a' && Prop'.beq b b'
  | .says p a, .says p' a' => decide (p = p') && Prop'.beq a a'
  | .speaksFor p q, .speaksFor p' q' => decide (p = p') && decide (q = q')
  | .at a ℓ, .at a' ℓ' => Prop'.beq a a' && decide (ℓ = ℓ')
  | .boxed o a, .boxed o' a' => decide (o = o') && Prop'.beq a a'
  | .within τ a, .within τ' a' => decide (τ = τ') && Prop'.beq a a'
  | .tensor a b, .tensor a' b' => Prop'.beq a a' && Prop'.beq b b'
  | .lolli a b, .lolli a' b' => Prop'.beq a a' && Prop'.beq b b'
  | _, _ => false

/-- Soundness of `Prop'.beq`: a `true` answer implies actual equality. The
proof is structural induction on the first argument with case analysis on
the second; `at` (with no `DecidableEq` on `Label`) is the only constructor
where `beq` is incomplete — `beq` returns `false` even when `at a ℓ = at a ℓ`,
so the implication direction trivially holds. -/
theorem Prop'.beq_eq_true_iff_eq : ∀ (φ ψ : Prop'),
    Prop'.beq φ ψ = true → φ = ψ := by
  intro φ
  induction φ
  case top =>
    intro ψ h
    cases ψ <;> simp_all [Prop'.beq]
  case bot =>
    intro ψ h
    cases ψ <;> simp_all [Prop'.beq]
  case atom n =>
    intro ψ h
    cases ψ <;> simp_all [Prop'.beq]
  case imp a b iha ihb =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    -- `simp` already pushes through Bool.and_eq_true into a conjunction.
    obtain ⟨ha, hb⟩ := h
    exact congr (congrArg Prop'.imp (iha _ ha)) (ihb _ hb)
  case and a b iha ihb =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨ha, hb⟩ := h
    exact congr (congrArg Prop'.and (iha _ ha)) (ihb _ hb)
  case or a b iha ihb =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨ha, hb⟩ := h
    exact congr (congrArg Prop'.or (iha _ ha)) (ihb _ hb)
  case «says» p a iha =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨hp, ha⟩ := h
    subst hp
    exact congrArg (Prop'.says p) (iha _ ha)
  case speaksFor p q =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨hp, hq⟩ := h
    subst hp; subst hq
    rfl
  case «at» a ℓ iha =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨ha, hℓ⟩ := h
    subst hℓ
    exact congr (congrArg Prop'.at (iha _ ha)) rfl
  case boxed o a iha =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨ho, ha⟩ := h
    subst ho
    exact congrArg (Prop'.boxed o) (iha _ ha)
  case within τ a iha =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨hτ, ha⟩ := h
    subst hτ
    exact congrArg (Prop'.within τ) (iha _ ha)
  case tensor a b iha ihb =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨ha, hb⟩ := h
    exact congr (congrArg Prop'.tensor (iha _ ha)) (ihb _ hb)
  case lolli a b iha ihb =>
    intro ψ h
    cases ψ <;> (try (simp [Prop'.beq] at h))
    obtain ⟨ha, hb⟩ := h
    exact congr (congrArg Prop'.lolli (iha _ ha)) (ihb _ hb)

/-- Reflexivity of `Prop'.beq`: every proposition compares equal to itself.
Load-bearing for T1 completeness — the App case of `decideLean` calls
`Prop'.beq` on the function's argument-type against the argument's
inferred type; for a `PropDeriv.impE` these must agree, so reflexivity
closes the comparison. -/
theorem Prop'.beq_refl : ∀ (φ : Prop'), Prop'.beq φ φ = true := by
  intro φ
  induction φ
  case top => rfl
  case bot => rfl
  case atom n => simp [Prop'.beq]
  case imp a b iha ihb => simp [Prop'.beq, iha, ihb]
  case and a b iha ihb => simp [Prop'.beq, iha, ihb]
  case or a b iha ihb => simp [Prop'.beq, iha, ihb]
  case «says» p a iha => simp [Prop'.beq, iha]
  case speaksFor p q => simp [Prop'.beq]
  case «at» a ℓ iha => simp [Prop'.beq, iha]
  case boxed o a iha => simp [Prop'.beq, iha]
  case within τ a iha => simp [Prop'.beq, iha]
  case tensor a b iha ihb => simp [Prop'.beq, iha, ihb]
  case lolli a b iha ihb => simp [Prop'.beq, iha, ihb]

/-! ## `decideLean` — Lean mirror of Rust `infer`.

Mirror of `crates/dlc-core/src/decide.rs::infer` for the propositional
fragment. Non-propositional Term constructors return `none`.

To keep the soundness proof tractable in this PR, the App case requires
the inferred function type to be an `Imp` and the argument's inferred
type to `Prop'.beq`-match. The Q4 follow-up extends this to the full
calculus's elimination forms (case, letTensor, letSays, sfExtract, etc.). -/
def decideLean (Γ : Ctx) : Term → Option Prop'
  | .var i =>
    match Γ.additive[i]? with
    | some φ => some φ
    | none =>
      -- var-L: singleton linear context, index 0.
      match Γ.linear, i with
      | [φ], 0 => some φ
      | _, _ => none
  | .lam φ body =>
    match decideLean (Ctx.consA φ Γ) body with
    | some ψ => some (Prop'.imp φ ψ)
    | none => none
  | .app f x =>
    match decideLean Γ f with
    | some (Prop'.imp φ ψ) =>
      match decideLean Γ x with
      | some φ' => if Prop'.beq φ φ' then some ψ else none
      | none => none
    | _ => none
  | .sign p m _sig =>
    match decideLean Γ m with
    | some φ => some (Prop'.says p φ)
    | none => none
  | .verify p m _sig =>
    -- says-E: M must have type `p says φ`; result is φ.
    match decideLean Γ m with
    | some (Prop'.says p' inner) =>
      if decide (p = p') then some inner else none
    | _ => none
  | .pair a b =>
    -- and-I: pairs of derivations produce `and`-typed terms.
    -- Use explicit nested matches so `split` in proofs peels predictably.
    match decideLean Γ a with
    | some α =>
      match decideLean Γ b with
      | some β => some (Prop'.and α β)
      | none => none
    | none => none
  | .fst a =>
    -- and-E-left: extract the left component.
    match decideLean Γ a with
    | some (Prop'.and φ _) => some φ
    | _ => none
  | .snd a =>
    -- and-E-right: extract the right component.
    match decideLean Γ a with
    | some (Prop'.and _ ψ) => some ψ
    | _ => none
  | .withinIntro τ m =>
    -- within-I: wraps the inner type with the within-τ modality.
    match decideLean Γ m with
    | some φ => some (Prop'.within τ φ)
    | none => none
  | .inl ψ a =>
    -- or-I-left: wrap φ into φ ∨ ψ.
    match decideLean Γ a with
    | some φ => some (Prop'.or φ ψ)
    | none => none
  | .inr φ a =>
    -- or-I-right: wrap ψ into φ ∨ ψ.
    match decideLean Γ a with
    | some ψ => some (Prop'.or φ ψ)
    | none => none
  | .tensorIntro a b =>
    -- tensor-I: multiplicative conjunction (linear pair).
    match decideLean Γ a with
    | some φ =>
      match decideLean Γ b with
      | some ψ => some (Prop'.tensor φ ψ)
      | none => none
    | none => none
  | .case s l r =>
    -- or-E: scrutinee must be or-typed; both branches must agree.
    match decideLean Γ s with
    | some (Prop'.or φ ψ) =>
      match decideLean (Ctx.consA φ Γ) l, decideLean (Ctx.consA ψ Γ) r with
      | some χL, some χR => if Prop'.beq χL χR then some χL else none
      | _, _ => none
    | _ => none
  | .letSays p s b =>
    -- says-elim let-binder: scrutinee must be `p says φ`; body lives
    -- in extended context with φ added; result is body's type ψ
    -- (the says modality is stripped by the let-binder).
    match decideLean Γ s with
    | some (Prop'.says p' φ) =>
      if decide (p = p') then
        decideLean (Ctx.consA φ Γ) b
      else none
    | _ => none
  | .sfExtract m =>
    -- sf-extract: from `p says (q ⇒ p)` extract `q ⇒ p`.
    match decideLean Γ m with
    | some (Prop'.says p_outer (Prop'.speaksFor q p_inner)) =>
      if decide (p_outer = p_inner) then
        some (Prop'.speaksFor q p_outer)
      else none
    | _ => none
  | .delegate m n =>
    -- delegate: M : p says (q ⇒ p), N : q says φ → (p ⊓ q) says φ.
    -- No-chain-splicing: speaks-for's q must match N's says-principal.
    match decideLean Γ m with
    | some (Prop'.says m_principal (Prop'.speaksFor q_outer p_outer)) =>
      if decide (p_outer = m_principal) then
        match decideLean Γ n with
        | some (Prop'.says n_principal n_inner) =>
          if decide (q_outer = n_principal) then
            some (Prop'.says (Principal.acting p_outer n_principal) n_inner)
          else none
        | _ => none
      else none
    | _ => none
  | .now _ =>
    -- `now τ` is the unit-like introduction form for `Top`. References
    -- no hypotheses, so always-typed at `Top` regardless of context.
    -- Mirrors Rust `Term::Now(_tau) => Some(Prop::Top)` in `decide.rs`.
    some Prop'.top
  | .attenuate m psi =>
    -- `attenuate M ψ`: narrowing along provable implication. Full Rust
    -- semantics trust the claimed `ψ`; here we accept only the
    -- *degenerate* case where `ψ = φ` (M's says-inner). This is a
    -- sound, strict subset — the impl witness for `φ ⊃ φ` is trivially
    -- `Term.var 0` in `Ctx.consA φ Ctx.empty` (via `Deriv.varA`).
    -- Non-degenerate attenuation requires a decision procedure for
    -- propositional implication, which is a separate substantial PR.
    match decideLean Γ m with
    | some (Prop'.says p phi) =>
      if Prop'.beq phi psi then some (Prop'.says p psi) else none
    | _ => none
  | .liftLabel ℓ m =>
    -- `lift_ℓ(M)`: introduce the IFC `at` modality. Whatever type
    -- `M` has, the result is `M`'s type at label `ℓ`. Mirrors Rust
    -- `Term::LiftLabel(label, m) => Some(Prop::At(m_ty, label))`.
    match decideLean Γ m with
    | some φ => some (Prop'.at φ ℓ)
    | none => none
  | .declassify ℓ' m π =>
    -- `declassify_ℓ'(M, π)`: controlled label lowering. Requires
    -- M : at φ ℓ and a policy-witness π : atom 0. Result is at φ ℓ'.
    -- Stricter than Rust (which ignores `_policy`); we enforce the
    -- policy-witness premise to keep decideLean sound vs Deriv.
    match decideLean Γ m with
    | some (Prop'.at φ _) =>
      match decideLean Γ π with
      | some (Prop'.atom 0) => some (Prop'.at φ ℓ')
      | _ => none
    | _ => none
  | .boxed _ _ _ =>
    -- FAIL-CLOSED, DEFERRED TO R5 OF THE T4 LADDER.
    --
    -- R3's job is to mirror `Term.boxed` into the hand-written Lean
    -- mechanically. Typing it here is not mechanical, and the attempt
    -- surfaced a real asymmetry worth recording before R5 picks it up:
    --
    --   * `decide.rs` IGNORES the obligation evidence -- its arm is
    --     `Term::Boxed(o, m, _evidence)`, returning `Prop::Boxed(o, ty(m))`.
    --   * `Deriv.boxI` REQUIRES `dN : Deriv Ctx.empty N (Prop'.atom 0)` --
    --     evidence, well-typed, in the EMPTY context.
    --
    -- So a Lean arm that faithfully mirrored the Rust would accept terms
    -- the calculus cannot derive, and `t1_propositional_soundness` would
    -- become unprovable -- correctly so, since it would be false. A
    -- faithful arm must instead check `decideLean Ctx.empty n = some
    -- (Prop'.atom 0)`, which is STRICTER than the Rust.
    --
    -- That asymmetry is not new: the `discharge` arm below already
    -- validates evidence its Rust counterpart ignores. R5 should decide
    -- whether decide.rs tightens or the Lean documents the gap, alongside
    -- `pendingObligations` and the non-vacuity witness.
    --
    -- Until then the checker REJECTS box introduction. Fail-closed: no
    -- theorem is weakened, and no term is accepted that the calculus
    -- cannot derive.
    none
  | .discharge m n =>
    -- `discharge(M, N)`: eliminate the `boxed O φ` modality with
    -- obligation evidence N : atom 0. Mirrors Rust `Term::Discharge`.
    --
    -- REACHABLE AS OF THE T4 LADDER'S R3. This branch was previously
    -- unreachable: `boxI` concluded at `Term.app`, so nothing could
    -- produce a `boxed` type for it to eliminate, and the comment here
    -- recorded that its soundness was "vacuously preserved". Now that
    -- `Deriv.boxI` concludes at `Term.boxed` and the arm above produces
    -- `Prop'.boxed`, this branch can actually match.
    match decideLean Γ m with
    | some (Prop'.boxed _ inner) =>
      match decideLean Γ n with
      | some (Prop'.atom 0) => some inner
      | _ => none
    | _ => none
  | .letTensor s b =>
    -- `let x⊗y = s in b`: scrutinee must be tensor-typed; body lives
    -- in context with two binders (φ at index 0, ψ at index 1). The
    -- shared body type is the result type χ.
    match decideLean Γ s with
    | some (Prop'.tensor φ ψ) =>
      -- `consA ψ Γ` puts ψ at head (additive = ψ :: Γ.additive). So
      -- `consA φ (consA ψ Γ)` yields additive = φ :: ψ :: Γ.additive,
      -- matching PropDeriv.letTensor's `(φ :: ψ :: Γₐ)` convention.
      decideLean (Ctx.consA φ (Ctx.consA ψ Γ)) b
    | _ => none

/-! ## T1 — Propositional soundness (the headline closure for this PR).

For the propositional fragment, restricted to additive contexts (no linear
hypotheses), `decideLean` produces only well-typed derivations.

This proves the soundness direction: `decideLean = some φ` implies a
derivation exists. The complementary completeness direction is
`t1_propositional_completeness` later in this file; together they yield
the `PropDeriv.decidable_nonempty` instance. -/
theorem t1_propositional_soundness (M : Term) :
    ∀ (Γₐ : List Prop') (φ : Prop'),
      M.isPropositional = true →
      decideLean { additive := Γₐ, linear := [] } M = some φ →
      Nonempty (Deriv { additive := Γₐ, linear := [] } M φ) := by
  induction M
  case var i =>
    intro Γₐ φ _ hdec
    -- decideLean unfolds to a match on Γ.additive[i]?; the linear:=[] branch
    -- of the var-L fallback never fires.
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ heq
      have hψφ : ψ = φ := Option.some.inj hdec
      subst hψφ
      exact ⟨Deriv.varA _ i _ heq⟩
    · -- additive lookup miss; the inner var-L match on linear:=[] never fires.
      split at hdec <;> simp_all
  case lam ψ body ih =>
    intro Γₐ φ hprop hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ' hbody
      have hφ : Prop'.imp ψ ψ' = φ := Option.some.inj hdec
      subst hφ
      have hprop' : body.isPropositional = true := by
        simp [Term.isPropositional] at hprop; exact hprop
      have hbody' : decideLean { additive := ψ :: Γₐ, linear := [] } body = some ψ' := by
        simpa [Ctx.consA] using hbody
      have ⟨dBody⟩ := ih (ψ :: Γₐ) ψ' hprop' hbody'
      exact ⟨Deriv.impI _ ψ ψ' body dBody⟩
    · simp at hdec
  case app f x ihf ihx =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropF, hpropX⟩ := hprop'
    unfold decideLean at hdec
    -- Outer split: decideLean Γ f.
    split at hdec
    · -- f's type is some (Prop'.imp α β).
      rename_i α β hf
      -- Inner split: decideLean Γ x.
      split at hdec
      · rename_i φ' hx
        by_cases hbeq : Prop'.beq α φ' = true
        · rw [if_pos hbeq] at hdec
          -- hdec : some β = some φ
          have hβφ : β = φ := Option.some.inj hdec
          -- hα : α = φ' from beq soundness
          have hα : α = φ' := Prop'.beq_eq_true_iff_eq α φ' hbeq
          -- Apply IHs at the types they actually produced.
          have ⟨dF⟩ := ihf Γₐ (Prop'.imp α β) hpropF hf
          have ⟨dX⟩ := ihx Γₐ φ' hpropX hx
          -- Realign dF to the goal-shape: rewrite α → φ', β → φ in dF.
          rw [hα, hβφ] at dF
          -- dF : Deriv ... f (Prop'.imp φ' φ); dX : Deriv ... x φ'.
          -- impE produces Deriv ... (Term.app f x) φ.
          -- impE now shifts its right premise by Γ₁.length (linear LEVELS).
          -- Here Γ₁ = [], so the shift is the identity (`shift_zero`).
          exact ⟨by simpa [shift_zero] using Deriv.impE Γₐ [] [] φ' φ f x dF dX⟩
        · rw [if_neg hbeq] at hdec
          simp at hdec
      · simp at hdec
    · simp at hdec
  case sign p m sig ihm =>
    intro Γₐ φ hprop hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ hm
      have hφ : Prop'.says p ψ = φ := Option.some.inj hdec
      subst hφ
      have hprop' : m.isPropositional = true := by
        simp [Term.isPropositional] at hprop; exact hprop
      have ⟨dM⟩ := ihm Γₐ ψ hprop' hm
      exact ⟨Deriv.saysI _ p ψ m sig dM⟩
    · simp at hdec
  case verify p m sig ihm =>
    intro Γₐ φ hprop hdec
    have hprop' : m.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    unfold decideLean at hdec
    split at hdec
    · rename_i p' inner hm
      by_cases hp : p = p'
      · rw [if_pos (decide_eq_true_iff.mpr hp)] at hdec
        have hinner : inner = φ := Option.some.inj hdec
        rw [← hp, hinner] at hm
        have ⟨dM⟩ := ihm Γₐ (Prop'.says p φ) hprop' hm
        exact ⟨Deriv.verifyE _ p φ m sig dM⟩
      · rw [if_neg (by simpa using hp)] at hdec
        cases hdec
    · cases hdec
  case pair a b ihA ihB =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropA, hpropB⟩ := hprop'
    -- Use explicit cases on decideLean's outputs to avoid split's
    -- aggressive flattening with tuple-style matches.
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some α =>
      cases hB : decideLean { additive := Γₐ, linear := [] } b with
      | none =>
        unfold decideLean at hdec
        rw [hA, hB] at hdec
        simp at hdec
      | some β =>
        unfold decideLean at hdec
        rw [hA, hB] at hdec
        -- hdec : some (Prop'.and α β) = some φ
        have hφ : Prop'.and α β = φ := Option.some.inj hdec
        rw [← hφ]
        have ⟨dA⟩ := ihA Γₐ α hpropA hA
        have ⟨dB⟩ := ihB Γₐ β hpropB hB
        exact ⟨Deriv.andI Γₐ α β a b dA dB⟩
  case fst a ihA =>
    intro Γₐ φ hprop hdec
    have hprop' : a.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some ty =>
      cases ty
      case and α β =>
        unfold decideLean at hdec
        rw [hA] at hdec
        have hφ : α = φ := Option.some.inj hdec
        rw [hφ] at hA
        have ⟨dA⟩ := ihA Γₐ (Prop'.and φ β) hprop' hA
        exact ⟨Deriv.andEL _ φ β a dA⟩
      all_goals (unfold decideLean at hdec; rw [hA] at hdec; simp at hdec)
  case snd a ihA =>
    intro Γₐ φ hprop hdec
    have hprop' : a.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some ty =>
      cases ty
      case and α β =>
        unfold decideLean at hdec
        rw [hA] at hdec
        have hφ : β = φ := Option.some.inj hdec
        rw [hφ] at hA
        have ⟨dA⟩ := ihA Γₐ (Prop'.and α φ) hprop' hA
        exact ⟨Deriv.andER _ α φ a dA⟩
      all_goals (unfold decideLean at hdec; rw [hA] at hdec; simp at hdec)
  case withinIntro τ m ihm =>
    intro Γₐ φ hprop hdec
    have hprop' : m.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ hm
      have hφ : Prop'.within τ ψ = φ := Option.some.inj hdec
      subst hφ
      have ⟨dM⟩ := ihm Γₐ ψ hprop' hm
      exact ⟨Deriv.withinI _ τ ψ m dM⟩
    · simp at hdec
  case inl ψ a ihA =>
    intro Γₐ φ hprop hdec
    have hprop' : a.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    unfold decideLean at hdec
    split at hdec
    · rename_i α hA
      have hφ : Prop'.or α ψ = φ := Option.some.inj hdec
      subst hφ
      have ⟨dA⟩ := ihA Γₐ α hprop' hA
      exact ⟨Deriv.orI_L _ α ψ a dA⟩
    · simp at hdec
  case inr φψ a ihA =>
    intro Γₐ φ hprop hdec
    have hprop' : a.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    unfold decideLean at hdec
    split at hdec
    · rename_i β hA
      have hφ : Prop'.or φψ β = φ := Option.some.inj hdec
      subst hφ
      have ⟨dA⟩ := ihA Γₐ β hprop' hA
      exact ⟨Deriv.orI_R _ φψ β a dA⟩
    · simp at hdec
  case tensorIntro a b ihA ihB =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropA, hpropB⟩ := hprop'
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some α =>
      cases hB : decideLean { additive := Γₐ, linear := [] } b with
      | none => unfold decideLean at hdec; rw [hA, hB] at hdec; simp at hdec
      | some β =>
        unfold decideLean at hdec
        rw [hA, hB] at hdec
        have hφ : Prop'.tensor α β = φ := Option.some.inj hdec
        rw [← hφ]
        have ⟨dA⟩ := ihA Γₐ α hpropA hA
        have ⟨dB⟩ := ihB Γₐ β hpropB hB
        exact ⟨by simpa [shift_zero] using Deriv.tensorI Γₐ [] [] α β a b dA dB⟩
  case case s l r ihS ihL ihR =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropS, hpropL, hpropR⟩ := hprop'
    cases hS : decideLean { additive := Γₐ, linear := [] } s with
    | none => simp [decideLean, hS] at hdec
    | some ty =>
      cases ty
      case or α β =>
        cases hL : decideLean { additive := α :: Γₐ, linear := [] } l with
        | none => simp [decideLean, hS, Ctx.consA, hL] at hdec
        | some χL =>
          cases hR : decideLean { additive := β :: Γₐ, linear := [] } r with
          | none => simp [decideLean, hS, Ctx.consA, hL, hR] at hdec
          | some χR =>
            simp only [decideLean, hS, Ctx.consA, hL, hR] at hdec
            -- hdec : (if Prop'.beq χL χR then some χL else none) = some φ
            by_cases hbeq : Prop'.beq χL χR = true
            · rw [if_pos hbeq] at hdec
              have hφ : χL = φ := Option.some.inj hdec
              have hχ : χL = χR := Prop'.beq_eq_true_iff_eq χL χR hbeq
              have ⟨dS⟩ := ihS Γₐ (Prop'.or α β) hpropS hS
              have ⟨dL⟩ := ihL (α :: Γₐ) χL hpropL hL
              have ⟨dR⟩ := ihR (β :: Γₐ) χR hpropR hR
              rw [hφ] at dL
              rw [← hχ, hφ] at dR
              exact ⟨Deriv.orE Γₐ α β φ s l r dS dL dR⟩
            · rw [if_neg hbeq] at hdec; cases hdec
      all_goals (simp [decideLean, hS] at hdec)
  case letSays p s b ihS ihB =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropS, hpropB⟩ := hprop'
    cases hS : decideLean { additive := Γₐ, linear := [] } s with
    | none => simp [decideLean, hS] at hdec
    | some ty =>
      cases ty
      case «says» p' α =>
        by_cases hp : p = p'
        · -- Reduce decideLean+hS+if to expose b's decideLean.
          have hdec' : decideLean { additive := α :: Γₐ, linear := [] } b
                        = some φ := by
            simpa [decideLean, hS, Ctx.consA, hp] using hdec
          have ⟨dS⟩ := ihS Γₐ (Prop'.says p' α) hpropS hS
          have ⟨dB⟩ := ihB (α :: Γₐ) φ hpropB hdec'
          rw [← hp] at dS
          exact ⟨Deriv.letSaysE Γₐ [] [] p α φ s b dS dB⟩
        · simp [decideLean, hS, hp] at hdec
      all_goals (simp [decideLean, hS] at hdec)
  case sfExtract m ihm =>
    intro Γₐ φ hprop hdec
    have hprop' : m.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some ty =>
      cases ty
      case «says» p_outer inner =>
        cases inner
        case speaksFor q p_inner =>
          by_cases hp : p_outer = p_inner
          · have hφ : Prop'.speaksFor q p_outer = φ := by
              simpa [decideLean, hM, hp] using hdec
            rw [← hφ]
            have ⟨dM⟩ := ihm Γₐ (Prop'.says p_outer (Prop'.speaksFor q p_inner)) hprop' hM
            rw [← hp] at dM
            exact ⟨Deriv.sfExtractE _ p_outer q m dM⟩
          · simp [decideLean, hM, hp] at hdec
        all_goals (simp [decideLean, hM] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case delegate m n ihm ihn =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropM, hpropN⟩ := hprop'
    -- Mirror the `sfExtract` pattern: enumerate `tyM`/`m_inner`/`tyN` via
    -- nested `cases`, with `all_goals (simp ... at hdec)` closing the
    -- non-matching alternatives. Put `by_cases` at the innermost level
    -- so the case-tag context is clean when we re-enter `case «says»`.
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «says» m_p m_inner =>
        cases m_inner
        case speaksFor q_outer p_outer =>
          cases hN : decideLean { additive := Γₐ, linear := [] } n with
          | none => simp [decideLean, hM, hN] at hdec
          | some tyN =>
            cases tyN
            case «says» n_p n_inner =>
              by_cases hpp : p_outer = m_p
              · by_cases hqn : q_outer = n_p
                · have hφ : Prop'.says (Principal.acting p_outer n_p) n_inner = φ := by
                    simpa [decideLean, hM, hN, hpp, hqn] using hdec
                  rw [← hφ]
                  have ⟨dM⟩ := ihm Γₐ (Prop'.says m_p (Prop'.speaksFor q_outer p_outer)) hpropM hM
                  have ⟨dN⟩ := ihn Γₐ (Prop'.says n_p n_inner) hpropN hN
                  rw [← hpp] at dM
                  rw [hqn] at dM
                  exact ⟨by simpa [shift_zero] using
                    Deriv.delegate Γₐ [] [] p_outer n_p n_inner m n dM dN⟩
                · simp [decideLean, hM, hN, hpp, hqn] at hdec
              · simp [decideLean, hM, hN, hpp] at hdec
            all_goals (simp [decideLean, hM, hN] at hdec)
        all_goals (simp [decideLean, hM] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case now τ =>
    intro Γₐ φ _ hdec
    -- decideLean (Term.now τ) = some Prop'.top, so φ = Top.
    simp [decideLean] at hdec
    subst hdec
    exact ⟨Deriv.now Γₐ τ⟩
  case attenuate m psi ihm =>
    intro Γₐ φ hprop hdec
    have hpropM : m.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    -- decideLean (attenuate m ψ): only accepts when m has type `says p ψ`
    -- (i.e., φ_inner = ψ). Result is `says p ψ`.
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «says» p phiM =>
        by_cases hψ : Prop'.beq phiM psi
        · -- phiM = psi (the degenerate case): result is says p psi.
          have hphi_eq_psi : phiM = psi := Prop'.beq_eq_true_iff_eq phiM psi hψ
          have hφ : Prop'.says p psi = φ := by
            simpa [decideLean, hM, hψ] using hdec
          rw [← hφ]
          have ⟨dM⟩ := ihm Γₐ (Prop'.says p phiM) hpropM hM
          rw [hphi_eq_psi] at dM
          -- Now dM : Deriv Γₐ m (says p psi). Apply Deriv.attenuate
          -- with witness Term.var 0 in Ctx.consA psi Ctx.empty.
          exact ⟨Deriv.attenuate _ p psi psi m (Term.var 0) dM
            (Deriv.varA { additive := [psi], linear := [] } 0 psi rfl)⟩
        · simp [decideLean, hM, hψ] at hdec
      all_goals (simp [decideLean, hM] at hdec)
  case liftLabel ℓ m ihm =>
    intro Γₐ φ hprop hdec
    have hpropM : m.isPropositional = true := by
      simp [Term.isPropositional] at hprop; exact hprop
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      have hφ : Prop'.at tyM ℓ = φ := by
        simpa [decideLean, hM] using hdec
      rw [← hφ]
      have ⟨dM⟩ := ihm Γₐ tyM hpropM hM
      exact ⟨Deriv.liftLabel _ tyM ℓ m dM⟩
  case declassify ℓ' m π ihm ihπ =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropM, hpropπ⟩ := hprop'
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «at» ψ _ℓ =>
        cases hπ : decideLean { additive := Γₐ, linear := [] } π with
        | none => simp [decideLean, hM, hπ] at hdec
        | some tyπ =>
          cases tyπ
          case atom n =>
            -- need n = 0 for the inner pattern match to succeed.
            cases n with
            | zero =>
              have hφ : Prop'.at ψ ℓ' = φ := by
                simpa [decideLean, hM, hπ] using hdec
              rw [← hφ]
              have ⟨dM⟩ := ihm Γₐ (Prop'.at ψ _ℓ) hpropM hM
              have ⟨dπ⟩ := ihπ Γₐ (Prop'.atom 0) hpropπ hπ
              exact ⟨Deriv.declassify _ ψ _ℓ ℓ' m π dM dπ⟩
            | succ k => simp [decideLean, hM, hπ] at hdec
          all_goals (simp [decideLean, hM, hπ] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case boxed o m n ihm ihn =>
    intro Γₐ φ _ hdec
    -- `decideLean` rejects box introduction (fail-closed until R5 of the
    -- T4 ladder -- see the `.boxed` arm), so the hypothesis is false.
    simp [decideLean] at hdec
  case discharge m n ihm ihn =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropM, hpropN⟩ := hprop'
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «boxed» O inner =>
        cases hN : decideLean { additive := Γₐ, linear := [] } n with
        | none => simp [decideLean, hM, hN] at hdec
        | some tyN =>
          cases tyN
          case atom k =>
            cases k with
            | zero =>
              have hφ : inner = φ := by
                simpa [decideLean, hM, hN] using hdec
              rw [← hφ]
              have ⟨dM⟩ := ihm Γₐ (Prop'.boxed O inner) hpropM hM
              have ⟨dN⟩ := ihn Γₐ (Prop'.atom 0) hpropN hN
              exact ⟨by simpa [shift_zero] using Deriv.discharge _ [] [] O inner m n dM dN⟩
            | succ _ => simp [decideLean, hM, hN] at hdec
          all_goals (simp [decideLean, hM, hN] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case letTensor s b ihs ihb =>
    intro Γₐ φ hprop hdec
    have hprop' := hprop
    simp [Term.isPropositional] at hprop'
    obtain ⟨hpropS, hpropB⟩ := hprop'
    cases hS : decideLean { additive := Γₐ, linear := [] } s with
    | none => simp [decideLean, hS] at hdec
    | some tyS =>
      cases tyS
      case tensor α β =>
        -- hdec : decideLean (consA α (consA β { additive := Γₐ, linear := [] })) b = some φ
        -- The consA-folded ctx equals { additive := α :: β :: Γₐ, linear := [] }.
        have hb : decideLean { additive := α :: β :: Γₐ, linear := [] } b = some φ := by
          simpa [decideLean, hS, Ctx.consA] using hdec
        have ⟨dS⟩ := ihs Γₐ (Prop'.tensor α β) hpropS hS
        have ⟨dB⟩ := ihb (α :: β :: Γₐ) φ hpropB hb
        exact ⟨Deriv.letTensorA _ α β φ s b dS dB⟩
      all_goals (simp [decideLean, hS] at hdec)
  -- All non-propositional constructors are rejected by `isPropositional`:
  -- isPropositional returns false, so the hypothesis is contradictory.
  all_goals (intro Γₐ φ hprop hdec; simp [Term.isPropositional] at hprop)

/-! ## `PropDeriv` — the propositional fragment of `Deriv`.

`Deriv` has 24 constructors with overlapping Term shapes: `Term.app` is
produced by `impE`, `saysE`, and `boxI`; `Term.var` by `varA`, `varL`,
and `weakenA` etc. The `decideLean` checker mirrors only the four
rules `varA`, `impI`, `impE`, `saysI`. To cleanly state T1 completeness
without ambiguity over which `Deriv` constructor was used, we factor
out a `PropDeriv` sub-inductive matching `decideLean`'s structure
exactly.

`PropDeriv` is faithfully embedded into `Deriv` by `propDeriv_to_deriv`
(structural identity), so anything proven about `Deriv` (subject
reduction, T4 obligation soundness, etc.) lifts to `PropDeriv`. -/
inductive PropDeriv : List Prop' → Term → Prop' → Type where
  /-- `var-A` — additive variable lookup. -/
  | varA (Γₐ : List Prop') (i : Nat) (φ : Prop')
      (h : Γₐ[i]? = some φ) :
      PropDeriv Γₐ (Term.var i) φ

  /-- `imp-I` — implication introduction. -/
  | impI (Γₐ : List Prop') (φ ψ : Prop') (M : Term)
      (d : PropDeriv (φ :: Γₐ) M ψ) :
      PropDeriv Γₐ (Term.lam φ M) (Prop'.imp φ ψ)

  /-- `imp-E` — implication elimination (linear:=[] so no context split). -/
  | impE (Γₐ : List Prop') (φ ψ : Prop') (M N : Term)
      (dM : PropDeriv Γₐ M (Prop'.imp φ ψ))
      (dN : PropDeriv Γₐ N φ) :
      PropDeriv Γₐ (Term.app M N) ψ

  /-- `says-I` — affirmation introduction with embedded signature. -/
  | saysI (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
          (sig : Signature)
      (d : PropDeriv Γₐ M φ) :
      PropDeriv Γₐ (Term.sign p M sig) (Prop'.says p φ)

  /-- `verify` — `says`-elimination at the symbolic level. Given a
  derivation that `M : p says φ`, the verify operation strips the
  modality and concludes `φ`. The cryptographic check is folded into
  `Deriv_K`; here the rule is symbolic. -/
  | verifyE (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
            (sig : Signature)
      (d : PropDeriv Γₐ M (Prop'.says p φ)) :
      PropDeriv Γₐ (Term.verify p M sig) φ

  /-- `and-I` — additive conjunction introduction (pair). -/
  | andI (Γₐ : List Prop') (φ ψ : Prop') (a b : Term)
      (dA : PropDeriv Γₐ a φ)
      (dB : PropDeriv Γₐ b ψ) :
      PropDeriv Γₐ (Term.pair a b) (Prop'.and φ ψ)

  /-- `and-E-left` — left projection. -/
  | andEL (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : PropDeriv Γₐ a (Prop'.and φ ψ)) :
      PropDeriv Γₐ (Term.fst a) φ

  /-- `and-E-right` — right projection. -/
  | andER (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : PropDeriv Γₐ a (Prop'.and φ ψ)) :
      PropDeriv Γₐ (Term.snd a) ψ

  /-- `within-I` — wrap `φ` with the time modality `◇_τ`. -/
  | withinI (Γₐ : List Prop') (τ : TimeBound) (φ : Prop') (M : Term)
      (d : PropDeriv Γₐ M φ) :
      PropDeriv Γₐ (Term.withinIntro τ M) (Prop'.within τ φ)

  /-- `or-I-left` — inject into the left disjunct. -/
  | orI_L (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : PropDeriv Γₐ a φ) :
      PropDeriv Γₐ (Term.inl ψ a) (Prop'.or φ ψ)

  /-- `or-I-right` — inject into the right disjunct. -/
  | orI_R (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : PropDeriv Γₐ a ψ) :
      PropDeriv Γₐ (Term.inr φ a) (Prop'.or φ ψ)

  /-- `tensor-I` — multiplicative (linear) conjunction. With
  `PropDeriv`'s implicit linear:=[], reduces to additive shape. -/
  | tensorI (Γₐ : List Prop') (φ ψ : Prop') (a b : Term)
      (dA : PropDeriv Γₐ a φ)
      (dB : PropDeriv Γₐ b ψ) :
      PropDeriv Γₐ (Term.tensorIntro a b) (Prop'.tensor φ ψ)

  /-- `or-E` — case-elimination of a disjunction. Both branches must
  produce the same result type χ. -/
  | orE (Γₐ : List Prop') (φ ψ χ : Prop') (S L R : Term)
      (dS : PropDeriv Γₐ S (Prop'.or φ ψ))
      (dL : PropDeriv (φ :: Γₐ) L χ)
      (dR : PropDeriv (ψ :: Γₐ) R χ) :
      PropDeriv Γₐ (Term.case S L R) χ

  /-- `says-extract` — explicit let-binder form of says-elim. Strips
  the `says` modality; the result type is the body's type ψ. -/
  | letSaysE (Γₐ : List Prop') (p : Principal) (φ ψ : Prop') (S B : Term)
      (dS : PropDeriv Γₐ S (Prop'.says p φ))
      (dB : PropDeriv (φ :: Γₐ) B ψ) :
      PropDeriv Γₐ (Term.letSays p S B) ψ

  /-- `sf-extract` — extract a speaks-for from `p says (q ⇒ p)`. -/
  | sfExtractE (Γₐ : List Prop') (p q : Principal) (M : Term)
      (d : PropDeriv Γₐ M (Prop'.says p (Prop'.speaksFor q p))) :
      PropDeriv Γₐ (Term.sfExtract M) (Prop'.speaksFor q p)

  /-- `delegate` — chain composition. From `M : p says (q ⇒ p)` and
  `N : q says φ`, conclude `delegate M N : (p ⊓ q) says φ`. The
  no-chain-splicing condition is built into the constructor — both
  M's says-principal and the speaks-for's `p` must be the same `p`,
  and the speaks-for's `q` must match N's says-principal. -/
  | delegate (Γₐ : List Prop') (p q : Principal) (φ : Prop') (M N : Term)
      (dM : PropDeriv Γₐ M (Prop'.says p (Prop'.speaksFor q p)))
      (dN : PropDeriv Γₐ N (Prop'.says q φ)) :
      PropDeriv Γₐ (Term.delegate M N) (Prop'.says (Principal.acting p q) φ)

  /-- `now τ` — unit-like introduction form for `Top`. References no
  hypotheses, so always-typed at `Top` regardless of context. The
  generalized `Deriv.now Γₐ τ` (admitting any additive context with
  empty linear context) makes the embedding `propDeriv_to_deriv` total
  for the `now` case. -/
  | now (Γₐ : List Prop') (τ : TimeBound) :
      PropDeriv Γₐ (Term.now τ) Prop'.top

  /-- `attenuate` (degenerate form). Accepts `Term.attenuate M φ` at
  type `Prop'.says p φ` when the claimed `ψ` equals `M`'s inner
  proposition `φ`. The non-degenerate `ψ ≠ φ` case requires a
  propositional-implication decision procedure (deferred). The
  embedding `propDeriv_to_deriv` uses `Deriv.varA [φ] 0 φ rfl` as the
  trivial impl witness for `φ ⊃ φ` in the singleton-additive context
  `Ctx.consA φ Ctx.empty`. -/
  | attenuate (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
      (d : PropDeriv Γₐ M (Prop'.says p φ)) :
      PropDeriv Γₐ (Term.attenuate M φ) (Prop'.says p φ)

  /-- `lift_ℓ(M)` — IFC label introduction. Pure introduction rule for
  the `at` modality. Mirrors `Deriv.liftLabel`. -/
  | liftLabel (Γₐ : List Prop') (φ : Prop') (ℓ : Label) (M : Term)
      (d : PropDeriv Γₐ M φ) :
      PropDeriv Γₐ (Term.liftLabel ℓ M) (Prop'.at φ ℓ)

  /-- `declassify_ℓ'(M, π)` — controlled IFC label lowering. Requires
  `M : φ @ ℓ` and a policy-witness `π : atom 0`. Mirrors
  `Deriv.declassify`. -/
  | declassify (Γₐ : List Prop') (φ : Prop') (ℓ ℓ' : Label) (M π : Term)
      (d : PropDeriv Γₐ M (Prop'.at φ ℓ))
      (dπ : PropDeriv Γₐ π (Prop'.atom 0)) :
      PropDeriv Γₐ (Term.declassify ℓ' M π) (Prop'.at φ ℓ')

  /-- `discharge(M, N)` — `□_O φ` elimination. Consumes a boxed
  derivation `M : boxed O φ` and obligation evidence `N : atom 0`,
  yielding `φ`. Note: PropDeriv has no `boxI` constructor (boxI uses
  `Term.app` which is ambiguous with impE in the propositional
  fragment), so this constructor is **dead** — `PropDeriv Γₐ M
  (Prop'.boxed _ _)` is uninhabited. Adding the constructor closes
  the syntactic surface for completeness; soundness is vacuously
  preserved. -/
  | discharge (Γₐ : List Prop') (O : Obligation) (φ : Prop') (M N : Term)
      (dM : PropDeriv Γₐ M (Prop'.boxed O φ))
      (dN : PropDeriv Γₐ N (Prop'.atom 0)) :
      PropDeriv Γₐ (Term.discharge M N) φ

  /-- `let x⊗y = S in B` (additive variant) — tensor elimination in
  the propositional fragment. Body context `φ :: ψ :: Γₐ` (φ at
  index 0). Matches `Reduce.lean`'s β-rule
  `subst (subst body (shift a 1 0)) b`. -/
  | letTensor (Γₐ : List Prop') (φ ψ χ : Prop') (S B : Term)
      (dS : PropDeriv Γₐ S (Prop'.tensor φ ψ))
      (dB : PropDeriv (φ :: ψ :: Γₐ) B χ) :
      PropDeriv Γₐ (Term.letTensor S B) χ

/-! ## Shift preservation — load-bearing lemma for subject reduction.

If `M` is well-typed under `Γl ++ Γr`, then shifting `M`'s free variables
by `Γm.length` above cutoff `Γl.length` produces a term well-typed
under `Γl ++ Γm ++ Γr`. Proven via the auxiliary `propDeriv_shift_aux`
to work around Lean's `induction` restriction on non-variable indices;
the auxiliary generalizes the context to a fresh variable plus an
equality hypothesis. `noncomputable def` because `PropDeriv` is
`Type`-valued (the result builds a constructive derivation). -/

private noncomputable def propDeriv_shift_aux
    {Γfull : List Prop'} {M : Term} {φ : Prop'}
    (d : PropDeriv Γfull M φ) :
    ∀ (Γl Γr Γm : List Prop'), Γfull = Γl ++ Γr →
      PropDeriv (Γl ++ Γm ++ Γr) (shift M Γm.length Γl.length) φ := by
  induction d with
  | varA _ i χ h =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    by_cases hcut : i < Γl.length
    · rw [if_pos hcut]
      apply PropDeriv.varA
      rw [List.getElem?_append_left (by simp; omega : i < (Γl ++ Γm).length)]
      rw [List.getElem?_append_left hcut]
      rw [List.getElem?_append_left hcut] at h
      exact h
    · rw [if_neg hcut]
      apply PropDeriv.varA
      have hi : Γl.length ≤ i := Nat.not_lt.mp hcut
      have hge : (Γl ++ Γm).length ≤ i + Γm.length := by simp; omega
      rw [List.getElem?_append_right hge]
      have hr : i + Γm.length - (Γl ++ Γm).length = i - Γl.length := by
        simp; omega
      rw [hr]
      rw [List.getElem?_append_right hi] at h
      exact h
  | impI _ χ ψ' M' _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    -- The inner derivation lives in `χ :: Γl ++ Γr = (χ :: Γl) ++ Γr`.
    have ih' := ih (χ :: Γl) Γr Γm (by simp [List.cons_append])
    exact PropDeriv.impI _ χ ψ' _ ih'
  | impE _ α β M' N' _ _ ihM ihN =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.impE _ α β _ _ (ihM Γl Γr Γm rfl) (ihN Γl Γr Γm rfl)
  | saysI _ p ψ' M' sig _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.saysI _ p ψ' _ sig (ih Γl Γr Γm rfl)
  | verifyE _ p ψ' M' sig _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.verifyE _ p ψ' _ sig (ih Γl Γr Γm rfl)
  | andI _ φ ψ a b _ _ ihA ihB =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.andI _ φ ψ _ _ (ihA Γl Γr Γm rfl) (ihB Γl Γr Γm rfl)
  | andEL _ φ ψ a _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.andEL _ φ ψ _ (ih Γl Γr Γm rfl)
  | andER _ φ ψ a _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.andER _ φ ψ _ (ih Γl Γr Γm rfl)
  | withinI _ τ φ M _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.withinI _ τ φ _ (ih Γl Γr Γm rfl)
  | orI_L _ φ ψ a _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.orI_L _ φ ψ _ (ih Γl Γr Γm rfl)
  | orI_R _ φ ψ a _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.orI_R _ φ ψ _ (ih Γl Γr Γm rfl)
  | tensorI _ φ ψ a b _ _ ihA ihB =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.tensorI _ φ ψ _ _ (ihA Γl Γr Γm rfl) (ihB Γl Γr Γm rfl)
  | orE _ φ ψ χ S L R _ _ _ ihS ihL ihR =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    have hL := ihL (φ :: Γl) Γr Γm (by simp [List.cons_append])
    have hR := ihR (ψ :: Γl) Γr Γm (by simp [List.cons_append])
    exact PropDeriv.orE _ φ ψ χ _ _ _ (ihS Γl Γr Γm rfl) hL hR
  | letSaysE _ p φ ψ S B _ _ ihS ihB =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    have hB := ihB (φ :: Γl) Γr Γm (by simp [List.cons_append])
    exact PropDeriv.letSaysE _ p φ ψ _ _ (ihS Γl Γr Γm rfl) hB
  | sfExtractE _ p q M _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.sfExtractE _ p q _ (ih Γl Γr Γm rfl)
  | delegate _ p q φ M N _ _ ihM ihN =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.delegate _ p q φ _ _ (ihM Γl Γr Γm rfl) (ihN Γl Γr Γm rfl)
  | now _ τ =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.now (Γl ++ Γm ++ Γr) τ
  | attenuate _ p φ M _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.attenuate _ p φ _ (ih Γl Γr Γm rfl)
  | liftLabel _ φ ℓ M _ ih =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.liftLabel _ φ ℓ _ (ih Γl Γr Γm rfl)
  | declassify _ φ ℓ ℓ' M π _ _ ihM ihπ =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.declassify _ φ ℓ ℓ' _ _ (ihM Γl Γr Γm rfl) (ihπ Γl Γr Γm rfl)
  | discharge _ O φ M N _ _ ihM ihN =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    exact PropDeriv.discharge _ O φ _ _ (ihM Γl Γr Γm rfl) (ihN Γl Γr Γm rfl)
  | letTensor _ φ ψ χ S B _ _ ihS ihB =>
    intro Γl Γr Γm hΓ
    subst hΓ
    unfold shift
    -- Body context φ :: ψ :: Γl ++ Γr → φ :: ψ :: Γl ++ Γm ++ Γr.
    have hB := ihB (φ :: ψ :: Γl) Γr Γm (by simp [List.cons_append])
    exact PropDeriv.letTensor _ φ ψ χ _ _ (ihS Γl Γr Γm rfl) hB

/-- Public-facing shift preservation, instantiated from
`propDeriv_shift_aux` with the trivial equality. -/
noncomputable def propDeriv_shift
    (Γl Γr : List Prop') (M : Term) (φ : Prop')
    (d : PropDeriv (Γl ++ Γr) M φ) (Γm : List Prop') :
    PropDeriv (Γl ++ Γm ++ Γr) (shift M Γm.length Γl.length) φ :=
  propDeriv_shift_aux d Γl Γr Γm rfl

/-- Convenience: weakening at the front of the context (insert one
hypothesis at index 0). Specializes `propDeriv_shift` with `Γl = []`
and `Γm = [ψ]`. -/
noncomputable def propDeriv_weaken_front (Γₐ : List Prop') (ψ : Prop')
    (M : Term) (φ : Prop')
    (d : PropDeriv Γₐ M φ) :
    PropDeriv (ψ :: Γₐ) (shift M 1 0) φ := by
  have := propDeriv_shift [] Γₐ M φ (by simpa using d) [ψ]
  simpa using this

/-! ## Substitution preservation — the key subject-reduction lemma.

If `M` is well-typed under `Γl ++ φ :: Γr` and `N : φ` under `Γr`, then
substituting `N` for the binder at index `Γl.length` in `M` preserves
typing under `Γl ++ Γr`. This is the classical de Bruijn substitution-
preservation theorem.

The variable case at the substitution-target index (`i = Γl.length`)
uses `propDeriv_shift` to lift `N` past the prefix `Γl`. The `impI`
case extends `Γl` by the bound variable; the IH carries through with
`Γl' = χ :: Γl`. -/

private noncomputable def propDeriv_substAt_aux
    {Γfull : List Prop'} {M : Term} {ψ : Prop'}
    (dM : PropDeriv Γfull M ψ) :
    ∀ (Γl Γr : List Prop') (φ : Prop'), Γfull = Γl ++ φ :: Γr →
    ∀ (N : Term), PropDeriv Γr N φ →
      PropDeriv (Γl ++ Γr) (substAt M N Γl.length) ψ := by
  induction dM with
  | varA _ i χ h =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    -- h : (Γl ++ φ :: Γr)[i]? = some χ
    unfold substAt
    -- Split on i vs Γl.length.
    by_cases heq : i = Γl.length
    · -- substAt at hit-position: shift N Γl.length 0.
      rw [if_pos heq]
      -- From h with i = Γl.length: (Γl ++ φ :: Γr)[Γl.length] = (φ :: Γr)[0] = some φ.
      -- So χ = φ.
      subst heq
      have hφ : χ = φ := by
        rw [List.getElem?_append_right (le_refl _)] at h
        simp at h
        exact h.symm
      subst hφ
      -- Goal: PropDeriv (Γl ++ Γr) (shift N Γl.length 0) χ.
      -- propDeriv_shift [] Γr N χ dN Γl :
      --   PropDeriv ([] ++ Γl ++ Γr) (shift N Γl.length [].length) χ
      --   = PropDeriv (Γl ++ Γr) (shift N Γl.length 0) χ
      have := propDeriv_shift [] Γr N χ (by simpa using dN) Γl
      simpa using this
    · rw [if_neg heq]
      by_cases hgt : i > Γl.length
      · rw [if_pos hgt]
        -- substAt = Term.var (i-1).
        apply PropDeriv.varA
        -- Show (Γl ++ Γr)[i-1]? = some χ.
        -- From h: (Γl ++ φ :: Γr)[i] = (φ :: Γr)[i - Γl.length] = Γr[i - Γl.length - 1] = some χ.
        have hge : Γl.length ≤ i := Nat.le_of_lt hgt
        rw [List.getElem?_append_right hge] at h
        -- h : (φ :: Γr)[i - Γl.length]? = some χ
        -- Now i - Γl.length ≥ 1 since hgt : i > Γl.length.
        have hpos : i - Γl.length > 0 := Nat.sub_pos_of_lt hgt
        -- (φ :: Γr)[i - Γl.length] = Γr[i - Γl.length - 1] for i - Γl.length > 0.
        have hcons : (φ :: Γr)[i - Γl.length]? = Γr[i - Γl.length - 1]? := by
          rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos) with ⟨k, hk⟩
          rw [hk]
          simp
        rw [hcons] at h
        -- Now (Γl ++ Γr)[i-1]? — show it equals Γr[i - Γl.length - 1]?
        have hile : Γl.length ≤ i - 1 := by omega
        rw [List.getElem?_append_right hile]
        have hr : i - 1 - Γl.length = i - Γl.length - 1 := by omega
        rw [hr]
        exact h
      · -- i ≤ Γl.length and i ≠ Γl.length: i < Γl.length.
        push_neg at hgt
        have hlt : i < Γl.length := lt_of_le_of_ne hgt heq
        rw [if_neg (Nat.not_lt_of_le hgt)]
        -- substAt = Term.var i.
        apply PropDeriv.varA
        rw [List.getElem?_append_left hlt]
        rw [List.getElem?_append_left hlt] at h
        exact h
  | impI _ χ ψ' M' _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    -- Inner d' : PropDeriv (χ :: Γl ++ φ :: Γr) M' ψ' = PropDeriv ((χ :: Γl) ++ φ :: Γr) M' ψ'.
    -- IH applied at (χ :: Γl):
    have ih' := ih (χ :: Γl) Γr φ (by simp [List.cons_append]) N dN
    exact PropDeriv.impI _ χ ψ' _ ih'
  | impE _ α β M' N' _ _ ihM ihN =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.impE _ α β _ _ (ihM Γl Γr φ rfl N dN) (ihN Γl Γr φ rfl N dN)
  | saysI _ p ψ' M' sig _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.saysI _ p ψ' _ sig (ih Γl Γr φ rfl N dN)
  | verifyE _ p ψ' M' sig _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.verifyE _ p ψ' _ sig (ih Γl Γr φ rfl N dN)
  | andI _ φ' ψ' a b _ _ ihA ihB =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.andI _ φ' ψ' _ _
      (ihA Γl Γr φ rfl N dN) (ihB Γl Γr φ rfl N dN)
  | andEL _ φ' ψ' a _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.andEL _ φ' ψ' _ (ih Γl Γr φ rfl N dN)
  | andER _ φ' ψ' a _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.andER _ φ' ψ' _ (ih Γl Γr φ rfl N dN)
  | withinI _ τ φ' M _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.withinI _ τ φ' _ (ih Γl Γr φ rfl N dN)
  | orI_L _ φ' ψ' a _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.orI_L _ φ' ψ' _ (ih Γl Γr φ rfl N dN)
  | orI_R _ φ' ψ' a _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.orI_R _ φ' ψ' _ (ih Γl Γr φ rfl N dN)
  | tensorI _ φ' ψ' a b _ _ ihA ihB =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.tensorI _ φ' ψ' _ _
      (ihA Γl Γr φ rfl N dN) (ihB Γl Γr φ rfl N dN)
  | orE _ φ' ψ' χ S L R _ _ _ ihS ihL ihR =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    have hL := ihL (φ' :: Γl) Γr φ (by simp [List.cons_append]) N dN
    have hR := ihR (ψ' :: Γl) Γr φ (by simp [List.cons_append]) N dN
    exact PropDeriv.orE _ φ' ψ' χ _ _ _ (ihS Γl Γr φ rfl N dN) hL hR
  | letSaysE _ p φ' ψ S B _ _ ihS ihB =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    have hB := ihB (φ' :: Γl) Γr φ (by simp [List.cons_append]) N dN
    exact PropDeriv.letSaysE _ p φ' ψ _ _ (ihS Γl Γr φ rfl N dN) hB
  | sfExtractE _ p q M _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.sfExtractE _ p q _ (ih Γl Γr φ rfl N dN)
  | delegate _ p q ψ M N _ _ ihM ihN =>
    intro Γl Γr φ hΓ Nval dNval
    subst hΓ
    unfold substAt
    exact PropDeriv.delegate _ p q ψ _ _
      (ihM Γl Γr φ rfl Nval dNval) (ihN Γl Γr φ rfl Nval dNval)
  | now _ τ =>
    intro Γl Γr φ hΓ _ _
    subst hΓ
    unfold substAt
    exact PropDeriv.now (Γl ++ Γr) τ
  | attenuate _ p ψ M _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.attenuate _ p ψ _ (ih Γl Γr φ rfl N dN)
  | liftLabel _ ψ ℓ M _ ih =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.liftLabel _ ψ ℓ _ (ih Γl Γr φ rfl N dN)
  | declassify _ ψ ℓ ℓ' M π _ _ ihM ihπ =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.declassify _ ψ ℓ ℓ' _ _
      (ihM Γl Γr φ rfl N dN) (ihπ Γl Γr φ rfl N dN)
  | discharge _ O ψ M Nb _ _ ihM ihN =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    exact PropDeriv.discharge _ O ψ _ _
      (ihM Γl Γr φ rfl N dN) (ihN Γl Γr φ rfl N dN)
  | letTensor _ α β χ S B _ _ ihS ihB =>
    intro Γl Γr φ hΓ N dN
    subst hΓ
    unfold substAt
    have hB := ihB (α :: β :: Γl) Γr φ (by simp [List.cons_append]) N dN
    exact PropDeriv.letTensor _ α β χ _ _ (ihS Γl Γr φ rfl N dN) hB

/-- Public-facing substitution preservation. -/
noncomputable def propDeriv_substAt
    (Γl Γr : List Prop') (φ ψ : Prop') (M N : Term)
    (dM : PropDeriv (Γl ++ φ :: Γr) M ψ)
    (dN : PropDeriv Γr N φ) :
    PropDeriv (Γl ++ Γr) (substAt M N Γl.length) ψ :=
  propDeriv_substAt_aux dM Γl Γr φ rfl N dN

/-- The "subst at depth 0" specialization: substitute N for the binder
at index 0 in M. -/
noncomputable def propDeriv_subst
    (Γₐ : List Prop') (φ ψ : Prop') (M N : Term)
    (dM : PropDeriv (φ :: Γₐ) M ψ)
    (dN : PropDeriv Γₐ N φ) :
    PropDeriv Γₐ (subst M N) ψ := by
  have := propDeriv_substAt [] Γₐ φ ψ M N (by simpa using dM) dN
  simpa [subst] using this

/-! ## Subject reduction — reduction preserves typing.

`step` has eight head redexes plus the 2026-07 CONGRUENCE (ξ) rules:
when an elimination form's scrutinee/function position is not the
redex shape, reduction descends into that position (see `Reduce.lean`).
The proof is by induction on the derivation. Head redexes follow from
substitution preservation (`propDeriv_subst`) plus syntax-directed
inversion of the premise derivation (`PropDeriv` has exactly one
constructor per subject shape); ξ-cases apply the induction hypothesis
for the reduced position and rebuild the same constructor. Value and
frozen-form subjects contradict `step M = some M'`. -/

noncomputable def propDeriv_subject_reduction
    (Γₐ : List Prop') (M : Term) (ψ : Prop')
    (d : PropDeriv Γₐ M ψ) :
    ∀ M', step M = some M' → PropDeriv Γₐ M' ψ := by
  induction d with
  | varA _ _ _ _ => intro M' h; simp [step] at h
  | impI _ _ _ _ _ _ => intro M' h; simp [step] at h
  | impE Γ α β f x dM dN ihM _ =>
    intro M' h
    unfold step at h
    split at h
    · -- β: f = lam _ body, M' = subst body x. Invert dM (impI is the
      -- only constructor at a lam subject), then substitution
      -- preservation closes the goal.
      simp only [Option.some.injEq] at h
      subst h
      cases dM with
      | impI _ _ _ _ dBody => exact propDeriv_subst _ _ _ _ _ dBody dN
    · -- ξ-app: reduction descends into the function position.
      cases hf : step f with
      | none => simp [hf] at h
      | some f' =>
        simp [hf] at h
        subst h
        exact PropDeriv.impE _ α β f' x (ihM f' hf) dN
  | saysI _ _ _ _ _ _ _ => intro M' h; simp [step] at h
  | verifyE _ _ _ _ _ _ _ =>
    -- `Term.verify` is a frozen elimination — `step` returns `none`.
    intro M' h; simp [step] at h
  | andI _ _ _ _ _ _ _ _ _ => intro M' h; simp [step] at h
  | andEL Γ α β a dA ihA =>
    intro M' h
    unfold step at h
    split at h
    · -- and-Eₗ-β: a = pair pa pb, M' = pa. Invert dA (only andI).
      simp only [Option.some.injEq] at h
      subst h
      cases dA with
      | andI _ _ _ _ _ dPA _ => exact dPA
    · -- ξ-fst.
      cases ha : step a with
      | none => simp [ha] at h
      | some a' =>
        simp [ha] at h
        subst h
        exact PropDeriv.andEL _ α β a' (ihA a' ha)
  | andER Γ α β a dA ihA =>
    intro M' h
    unfold step at h
    split at h
    · -- and-Eᵣ-β: a = pair pa pb, M' = pb.
      simp only [Option.some.injEq] at h
      subst h
      cases dA with
      | andI _ _ _ _ _ _ dPB => exact dPB
    · -- ξ-snd.
      cases ha : step a with
      | none => simp [ha] at h
      | some a' =>
        simp [ha] at h
        subst h
        exact PropDeriv.andER _ α β a' (ihA a' ha)
  | withinI _ _ _ _ _ _ => intro M' h; simp [step] at h
  | orI_L _ _ _ _ _ _ => intro M' h; simp [step] at h
  | orI_R _ _ _ _ _ _ => intro M' h; simp [step] at h
  | tensorI _ _ _ _ _ _ _ _ _ => intro M' h; simp [step] at h
  | orE Γ α β χ S L R dS dL dR ihS _ _ =>
    intro M' h
    unfold step at h
    split at h
    · -- or-E-β (inl): M' = subst L va.
      simp only [Option.some.injEq] at h
      subst h
      cases dS with
      | orI_L _ _ _ _ dVA => exact propDeriv_subst _ _ _ _ _ dL dVA
    · -- or-E-β (inr): M' = subst R va.
      simp only [Option.some.injEq] at h
      subst h
      cases dS with
      | orI_R _ _ _ _ dVA => exact propDeriv_subst _ _ _ _ _ dR dVA
    · -- ξ-case on the scrutinee.
      cases hs : step S with
      | none => simp [hs] at h
      | some S' =>
        simp [hs] at h
        subst h
        exact PropDeriv.orE _ α β χ S' L R (ihS S' hs) dL dR
  | letSaysE Γ p α β S B dS dB ihS _ =>
    intro M' h
    unfold step at h
    split at h
    · -- S = sign p' m sig; the head rule guards on p = p'.
      split at h
      · -- says-extract-β: M' = subst B m. Inversion of dS (saysI is
        -- the only constructor at a sign subject) identifies the
        -- principals, independently of the if-guard.
        simp only [Option.some.injEq] at h
        subst h
        cases dS with
        | saysI _ _ _ _ _ dM => exact propDeriv_subst _ _ _ _ _ dB dM
      · -- p ≠ p': step returned none — contradiction.
        simp at h
    · -- ξ-letsays on the scrutinee.
      cases hs : step S with
      | none => simp [hs] at h
      | some S' =>
        simp [hs] at h
        subst h
        exact PropDeriv.letSaysE _ p α β S' B (ihS S' hs) dB
  | sfExtractE Γ p q m dM ihM =>
    intro M' h
    unfold step at h
    split at h
    · -- sf-extract-β: m = sign _ inner _, M' = inner.
      simp only [Option.some.injEq] at h
      subst h
      cases dM with
      | saysI _ _ _ _ _ dInner => exact dInner
    · -- ξ-sfextract.
      cases hm : step m with
      | none => simp [hm] at h
      | some m' =>
        simp [hm] at h
        subst h
        exact PropDeriv.sfExtractE _ p q m' (ihM m' hm)
  | delegate Γ p q α m n dM dN ihM ihN =>
    intro M' h
    unfold step at h
    split at h
    · -- delegate-β: both positions are signs. Inversion forces the
      -- sign principals to be p and q; rebuild with saysI.
      simp only [Option.some.injEq] at h
      subst h
      cases dM with
      | saysI _ _ _ _ _ _ =>
        cases dN with
        | saysI _ _ _ _ _ dInnerN =>
          exact PropDeriv.saysI _ (Principal.acting p q) α _ _ dInnerN
    · -- ξ-delegate (right): left is a sign, right position reduces.
      cases hn : step n with
      | none => simp [hn] at h
      | some n' =>
        simp [hn] at h
        subst h
        exact PropDeriv.delegate _ p q α _ n' dM (ihN n' hn)
    · -- ξ-delegate (left): left position reduces.
      cases hm : step m with
      | none => simp [hm] at h
      | some m' =>
        simp [hm] at h
        subst h
        exact PropDeriv.delegate _ p q α m' n (ihM m' hm) dN
  | now _ _ =>
    -- `Term.now τ` is irreducible — `step` rejects it. Vacuous.
    intro M' h; simp [step] at h
  | attenuate _ _ _ _ _ _ =>
    -- `Term.attenuate M φ` is a frozen elimination — vacuous.
    intro M' h; simp [step] at h
  | liftLabel _ _ _ _ _ _ =>
    -- `Term.liftLabel ℓ M` is a value — vacuous.
    intro M' h; simp [step] at h
  | declassify _ _ _ _ _ _ _ _ _ _ =>
    -- `Term.declassify ℓ' M π` is a frozen elimination — vacuous.
    intro M' h; simp [step] at h
  | discharge Γ O φ m n dM dN ihM _ =>
    -- No longer vacuous: R4 gave `discharge` a redex (discharge-beta).
    intro M' h
    unfold step at h
    split at h
    · -- discharge-beta: m = boxed _ inner _, M' = inner.
      --
      -- Unreachable in THIS fragment, and provably so rather than by
      -- assertion: `PropDeriv` has no rule concluding at `Term.boxed`
      -- (box introduction is a `Deriv`-only rule), so `dM` -- which types
      -- the scrutinee -- is uninhabited here. `cases dM` closes the goal
      -- with zero subgoals.
      --
      -- The full-`Deriv` version of this case is where discharge-beta
      -- carries real content, and it is R5's multiset-accounting work.
      cases dM
    · -- xi-discharge: reduce the scrutinee in place.
      cases hm : step m with
      | none => simp [hm] at h
      | some m' =>
        simp [hm] at h
        subst h
        exact PropDeriv.discharge _ O φ m' n (ihM m' hm) dN
  | letTensor Γ α β χ S B dS dB ihS _ =>
    intro M' h
    unfold step at h
    split at h
    · -- tensor-E-β: S = tensorIntro a b,
      -- M' = subst (subst B (shift a 1 0)) b. Weaken a's derivation
      -- past the β-binder, then substitute twice (see the shift
      -- comment on `Reduce.lean`'s letTensor redex).
      simp only [Option.some.injEq] at h
      subst h
      cases dS
      rename_i dA dB'
      have dA' := propDeriv_weaken_front _ β _ α dA
      have h1 := propDeriv_subst _ _ _ _ _ dB dA'
      exact propDeriv_subst _ _ _ _ _ h1 dB'
    · -- ξ-lettensor on the scrutinee.
      cases hs : step S with
      | none => simp [hs] at h
      | some S' =>
        simp [hs] at h
        subst h
        exact PropDeriv.letTensor _ α β χ S' B (ihS S' hs) dB

/-- Structural embedding from `PropDeriv` into `Deriv`. Constructively
shows the propositional fragment is a faithful sub-typing-judgment. -/
noncomputable def propDeriv_to_deriv :
    ∀ (Γₐ : List Prop') (M : Term) (φ : Prop'),
      PropDeriv Γₐ M φ →
      Deriv { additive := Γₐ, linear := [] } M φ := by
  intro Γₐ M φ d
  induction d with
  | varA Γₐ i φ h => exact Deriv.varA _ i φ h
  | impI Γₐ φ ψ M _ ih => exact Deriv.impI _ φ ψ M ih
  | impE Γₐ φ ψ M N _ _ ihM ihN =>
      -- impE wants Γ₁ ++ Γ₂ = []; both empty works.
      -- Γ₁ = [] so impE's level-shift on the right premise is the identity.
      exact by simpa [shift_zero] using Deriv.impE Γₐ [] [] φ ψ M N ihM ihN
  | saysI Γₐ p φ M sig _ ih => exact Deriv.saysI _ p φ M sig ih
  | verifyE Γₐ p φ M sig _ ih => exact Deriv.verifyE _ p φ M sig ih
  | andI Γₐ φ ψ a b _ _ ihA ihB =>
      exact Deriv.andI Γₐ φ ψ a b ihA ihB
  | andEL Γₐ φ ψ a _ ih => exact Deriv.andEL _ φ ψ a ih
  | andER Γₐ φ ψ a _ ih => exact Deriv.andER _ φ ψ a ih
  | withinI Γₐ τ φ M _ ih => exact Deriv.withinI _ τ φ M ih
  | orI_L Γₐ φ ψ a _ ih => exact Deriv.orI_L _ φ ψ a ih
  | orI_R Γₐ φ ψ a _ ih => exact Deriv.orI_R _ φ ψ a ih
  | tensorI Γₐ φ ψ a b _ _ ihA ihB =>
      exact by simpa [shift_zero] using Deriv.tensorI _ [] [] φ ψ a b ihA ihB
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
      exact Deriv.orE _ φ ψ χ S L R ihS ihL ihR
  | letSaysE Γₐ p φ ψ S B _ _ ihS ihB =>
      exact Deriv.letSaysE Γₐ [] [] p φ ψ S B ihS ihB
  | sfExtractE Γₐ p q M _ ih =>
      exact Deriv.sfExtractE _ p q M ih
  | delegate Γₐ p q φ M N _ _ ihM ihN =>
      exact by simpa [shift_zero] using Deriv.delegate _ [] [] p q φ M N ihM ihN
  | now Γₐ τ =>
      exact Deriv.now Γₐ τ
  | attenuate Γₐ p φ M _ ih =>
      -- Trivial impl witness: `Term.var 0 : φ` in `consA φ Ctx.empty`.
      exact Deriv.attenuate _ p φ φ M (Term.var 0) ih
        (Deriv.varA { additive := [φ], linear := [] } 0 φ rfl)
  | liftLabel Γₐ φ ℓ M _ ih =>
      exact Deriv.liftLabel _ φ ℓ M ih
  | declassify Γₐ φ ℓ ℓ' M π _ _ ihM ihπ =>
      exact Deriv.declassify _ φ ℓ ℓ' M π ihM ihπ
  | discharge Γₐ O φ M N _ _ ihM ihN =>
      exact by simpa [shift_zero] using Deriv.discharge _ [] [] O φ M N ihM ihN
  | letTensor Γₐ φ ψ χ S B _ _ ihS ihB =>
      exact Deriv.letTensorA _ φ ψ χ S B ihS ihB

/-! ## T1 — Propositional completeness (the other direction). -/

/-- T1 propositional completeness: every `PropDeriv` is found by
`decideLean`. The induction is on `PropDeriv` directly — by definition
of `PropDeriv` only the four propositional rules apply, so
`decideLean`'s structure matches exactly. -/
theorem t1_propositional_completeness :
    ∀ (Γₐ : List Prop') (M : Term) (φ : Prop'),
      PropDeriv Γₐ M φ →
      decideLean { additive := Γₐ, linear := [] } M = some φ := by
  intro Γₐ M φ d
  induction d with
  | varA Γₐ i φ h =>
    -- decideLean of Term.var i in {Γₐ, []} returns Γₐ[i]?.
    unfold decideLean
    rw [h]
  | impI Γₐ φ ψ M _ ih =>
    -- decideLean of Term.lam φ M = some (Prop'.imp φ ψ) when the body
    -- check returns some ψ in the extended context. The IH gives that.
    unfold decideLean
    -- IH: decideLean (Ctx.consA φ {Γₐ, []}) M = some ψ.
    -- Ctx.consA φ {Γₐ, []} = { additive := φ::Γₐ, linear := [] }.
    have hbody : decideLean (Ctx.consA φ { additive := Γₐ, linear := [] }) M
                  = some ψ := by
      simpa [Ctx.consA] using ih
    rw [hbody]
  | impE Γₐ φ ψ M N _ _ ihM ihN =>
    -- decideLean of Term.app: match on dM's result, must be Imp.
    unfold decideLean
    rw [ihM, ihN]
    -- The if-condition is Prop'.beq φ φ, which is true by refl.
    simp [Prop'.beq_refl]
  | saysI Γₐ p φ M sig _ ih =>
    unfold decideLean
    rw [ih]
  | verifyE Γₐ p φ M sig _ ih =>
    -- IH: decideLean Γₐ M = some (Prop'.says p φ).
    -- decideLean (Term.verify p M sig) matches on the IH; if decide(p=p)
    -- returns some φ. decide(p = p) reduces to true.
    unfold decideLean
    rw [ih]
    simp
  | andI Γₐ φ ψ a b _ _ ihA ihB =>
    unfold decideLean
    rw [ihA, ihB]
  | andEL Γₐ φ ψ a _ ih =>
    unfold decideLean
    rw [ih]
  | andER Γₐ φ ψ a _ ih =>
    unfold decideLean
    rw [ih]
  | withinI Γₐ τ φ M _ ih =>
    unfold decideLean
    rw [ih]
  | orI_L Γₐ φ ψ a _ ih =>
    unfold decideLean
    rw [ih]
  | orI_R Γₐ φ ψ a _ ih =>
    unfold decideLean
    rw [ih]
  | tensorI Γₐ φ ψ a b _ _ ihA ihB =>
    unfold decideLean
    rw [ihA, ihB]
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
    -- decideLean of Term.case matches on scrutinee = some (or φ ψ), then
    -- checks branch types via Prop'.beq χ χ which is refl-true.
    unfold decideLean
    simp only [ihS, Ctx.consA, ihL, ihR, Prop'.beq_refl, if_true]
  | letSaysE Γₐ p φ ψ S B _ _ ihS ihB =>
    unfold decideLean
    simp [ihS, Ctx.consA, ihB]
  | sfExtractE Γₐ p q M _ ih =>
    unfold decideLean
    simp [ih]
  | delegate Γₐ p q φ M N _ _ ihM ihN =>
    unfold decideLean
    simp [ihM, ihN]
  | now Γₐ τ =>
    -- decideLean unfolds to `some Prop'.top` for any context.
    unfold decideLean
    rfl
  | attenuate Γₐ p φ M _ ih =>
    -- decideLean (attenuate M φ): produces `some (says p φ)` since
    -- φ = φ (the degenerate case the constructor encodes).
    unfold decideLean
    simp [ih, Prop'.beq_refl]
  | liftLabel Γₐ φ ℓ M _ ih =>
    -- decideLean (liftLabel ℓ M) = some (at φ ℓ).
    unfold decideLean
    simp [ih]
  | declassify Γₐ φ ℓ ℓ' M π _ _ ihM ihπ =>
    -- decideLean (declassify ℓ' M π) = some (at φ ℓ').
    unfold decideLean
    simp [ihM, ihπ]
  | discharge Γₐ O φ M N _ _ ihM ihN =>
    -- decideLean (discharge M N) = some φ (when both premises check).
    unfold decideLean
    simp [ihM, ihN]
  | letTensor Γₐ φ ψ χ S B _ _ ihS ihB =>
    -- decideLean (letTensor S B): scrutinee gives tensor, body gives χ
    -- in extended context.
    unfold decideLean
    simp [ihS, Ctx.consA, ihB]

/-! ## Inversion lemmas — the term shape determines the constructor.

For each `Term` constructor in the propositional fragment, `PropDeriv`
has exactly one corresponding rule. These four inversion lemmas extract
the sub-derivations (and any propositional side conditions) from a
`PropDeriv` over a specific term shape. -/

/-- Inversion for `PropDeriv` at a variable: only `varA` applies. -/
theorem PropDeriv_var_inv {Γₐ : List Prop'} {i : Nat} {φ : Prop'} :
    PropDeriv Γₐ (Term.var i) φ → Γₐ[i]? = some φ
  | .varA _ _ _ h => h

/-- Inversion for `PropDeriv` at a lambda: only `impI` applies, the
result type must be an implication, and the body has the codomain
type in the extended context. -/
noncomputable def PropDeriv_lam_inv {Γₐ : List Prop'} {χ : Prop'} {M' : Term}
    {φ : Prop'} :
    PropDeriv Γₐ (Term.lam χ M') φ →
    Σ' ψ' : Prop', PLift (φ = Prop'.imp χ ψ') × PropDeriv (χ :: Γₐ) M' ψ'
  | .impI _ _ ψ' _ d => ⟨ψ', .up rfl, d⟩

/-- Inversion for `PropDeriv` at an application: only `impE` applies,
giving an intermediate type `α` such that the function has type
`α → φ` and the argument has type `α`. -/
noncomputable def PropDeriv_app_inv {Γₐ : List Prop'} {f x : Term} {φ : Prop'} :
    PropDeriv Γₐ (Term.app f x) φ →
    Σ' α : Prop', PropDeriv Γₐ f (Prop'.imp α φ) × PropDeriv Γₐ x α
  | .impE _ α _ _ _ dM dN => ⟨α, dM, dN⟩

/-- Inversion for `PropDeriv` at a signed term: only `saysI` applies,
the result type must be a `says`, and the inner term has the inner
proposition. -/
noncomputable def PropDeriv_sign_inv {Γₐ : List Prop'} {p : Principal}
    {m : Term} {sig : Signature} {φ : Prop'} :
    PropDeriv Γₐ (Term.sign p m sig) φ →
    Σ' ψ : Prop', PLift (φ = Prop'.says p ψ) × PropDeriv Γₐ m ψ
  | .saysI _ _ ψ _ _ d => ⟨ψ, .up rfl, d⟩

/-! ## Type uniqueness — every PropDeriv pins down a unique type. -/

/-- Type uniqueness for `PropDeriv`: if two propositional derivations
exist for the same term in the same context, they assign the same type.
Follows directly from `t1_propositional_completeness` — both
derivations imply `decideLean` returns the same `some _` for the term,
and `Option.some.inj` extracts the propositional equality. -/
theorem PropDeriv_unique_type (Γₐ : List Prop') (M : Term) (φ ψ : Prop')
    (d₁ : PropDeriv Γₐ M φ) (d₂ : PropDeriv Γₐ M ψ) : φ = ψ := by
  have h₁ := t1_propositional_completeness Γₐ M φ d₁
  have h₂ := t1_propositional_completeness Γₐ M ψ d₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## Soundness landed in `PropDeriv`.

`t1_propositional_soundness` produces a `Deriv`; the corresponding
`PropDeriv` version below produces the propositional-fragment witness
needed for the `Decidable` instance. The proof mirrors the soundness
case work but lands in the smaller inductive. -/

/-- Soundness of `decideLean` valued in `PropDeriv` (the propositional
fragment). Mirrors `t1_propositional_soundness` case-for-case. -/
noncomputable def t1_propositional_soundness_prop (M : Term) :
    ∀ (Γₐ : List Prop') (φ : Prop'),
      decideLean { additive := Γₐ, linear := [] } M = some φ →
      PropDeriv Γₐ M φ := by
  induction M
  case var i =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ heq
      have : ψ = φ := Option.some.inj hdec
      subst this
      exact PropDeriv.varA _ i _ heq
    · split at hdec <;> simp_all
  case lam ψ body ih =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ' hbody
      have hφ : Prop'.imp ψ ψ' = φ := Option.some.inj hdec
      subst hφ
      have hbody' : decideLean { additive := ψ :: Γₐ, linear := [] } body
                      = some ψ' := by
        simpa [Ctx.consA] using hbody
      exact PropDeriv.impI _ ψ ψ' body (ih _ _ hbody')
    · simp at hdec
  case app f x ihf ihx =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i α β hf
      split at hdec
      · rename_i φ' hx
        by_cases hbeq : Prop'.beq α φ' = true
        · rw [if_pos hbeq] at hdec
          -- hdec : some β = some φ
          have hβφ : β = φ := Option.some.inj hdec
          have hα : α = φ' := Prop'.beq_eq_true_iff_eq α φ' hbeq
          -- Apply IHs at the types they actually produced.
          have dF := ihf Γₐ (Prop'.imp α β) hf
          have dX := ihx Γₐ φ' hx
          -- Realign dF to the goal-shape: rewrite α → φ', β → φ in dF.
          rw [hα, hβφ] at dF
          exact PropDeriv.impE _ φ' φ f x dF dX
        · rw [if_neg hbeq] at hdec; cases hdec
      · cases hdec
    · cases hdec
  case sign p m sig ihm =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ hm
      have hφ : Prop'.says p ψ = φ := Option.some.inj hdec
      subst hφ
      exact PropDeriv.saysI _ p ψ m sig (ihm _ _ hm)
    · simp at hdec
  case verify p m sig ihm =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i p' inner hm
      by_cases hp : p = p'
      · rw [if_pos (decide_eq_true_iff.mpr hp)] at hdec
        have hinner : inner = φ := Option.some.inj hdec
        rw [← hp, hinner] at hm
        exact PropDeriv.verifyE _ p φ m sig (ihm _ _ hm)
      · rw [if_neg (by simpa using hp)] at hdec
        cases hdec
    · cases hdec
  case pair a b ihA ihB =>
    intro Γₐ φ hdec
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some α =>
      cases hB : decideLean { additive := Γₐ, linear := [] } b with
      | none =>
        unfold decideLean at hdec
        rw [hA, hB] at hdec
        simp at hdec
      | some β =>
        unfold decideLean at hdec
        rw [hA, hB] at hdec
        have hφ : Prop'.and α β = φ := Option.some.inj hdec
        rw [← hφ]
        exact PropDeriv.andI _ α β _ _ (ihA _ _ hA) (ihB _ _ hB)
  case fst a ihA =>
    intro Γₐ φ hdec
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some ty =>
      cases ty
      case and α β =>
        unfold decideLean at hdec
        rw [hA] at hdec
        have hφ : α = φ := Option.some.inj hdec
        rw [hφ] at hA
        exact PropDeriv.andEL _ φ β _ (ihA _ _ hA)
      all_goals (unfold decideLean at hdec; rw [hA] at hdec; simp at hdec)
  case snd a ihA =>
    intro Γₐ φ hdec
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some ty =>
      cases ty
      case and α β =>
        unfold decideLean at hdec
        rw [hA] at hdec
        have hφ : β = φ := Option.some.inj hdec
        rw [hφ] at hA
        exact PropDeriv.andER _ α φ _ (ihA _ _ hA)
      all_goals (unfold decideLean at hdec; rw [hA] at hdec; simp at hdec)
  case withinIntro τ m ihm =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i ψ hm
      have hφ : Prop'.within τ ψ = φ := Option.some.inj hdec
      subst hφ
      exact PropDeriv.withinI _ τ ψ m (ihm _ _ hm)
    · simp at hdec
  case inl ψ a ihA =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i α hA
      have hφ : Prop'.or α ψ = φ := Option.some.inj hdec
      subst hφ
      exact PropDeriv.orI_L _ α ψ a (ihA _ _ hA)
    · simp at hdec
  case inr φψ a ihA =>
    intro Γₐ φ hdec
    unfold decideLean at hdec
    split at hdec
    · rename_i β hA
      have hφ : Prop'.or φψ β = φ := Option.some.inj hdec
      subst hφ
      exact PropDeriv.orI_R _ φψ β a (ihA _ _ hA)
    · simp at hdec
  case tensorIntro a b ihA ihB =>
    intro Γₐ φ hdec
    cases hA : decideLean { additive := Γₐ, linear := [] } a with
    | none => unfold decideLean at hdec; rw [hA] at hdec; simp at hdec
    | some α =>
      cases hB : decideLean { additive := Γₐ, linear := [] } b with
      | none => unfold decideLean at hdec; rw [hA, hB] at hdec; simp at hdec
      | some β =>
        unfold decideLean at hdec
        rw [hA, hB] at hdec
        have hφ : Prop'.tensor α β = φ := Option.some.inj hdec
        rw [← hφ]
        exact PropDeriv.tensorI _ α β _ _ (ihA _ _ hA) (ihB _ _ hB)
  case case s l r ihS ihL ihR =>
    intro Γₐ φ hdec
    cases hS : decideLean { additive := Γₐ, linear := [] } s with
    | none => simp [decideLean, hS] at hdec
    | some ty =>
      cases ty
      case or α β =>
        cases hL : decideLean { additive := α :: Γₐ, linear := [] } l with
        | none => simp [decideLean, hS, Ctx.consA, hL] at hdec
        | some χL =>
          cases hR : decideLean { additive := β :: Γₐ, linear := [] } r with
          | none => simp [decideLean, hS, Ctx.consA, hL, hR] at hdec
          | some χR =>
            simp only [decideLean, hS, Ctx.consA, hL, hR] at hdec
            by_cases hbeq : Prop'.beq χL χR = true
            · rw [if_pos hbeq] at hdec
              have hφ : χL = φ := Option.some.inj hdec
              have hχ : χL = χR := Prop'.beq_eq_true_iff_eq χL χR hbeq
              rw [hφ] at hL
              rw [← hχ, hφ] at hR
              exact PropDeriv.orE _ α β φ s l r (ihS _ _ hS) (ihL _ _ hL) (ihR _ _ hR)
            · rw [if_neg hbeq] at hdec; cases hdec
      all_goals (simp [decideLean, hS] at hdec)
  case letSays p s b ihS ihB =>
    intro Γₐ φ hdec
    cases hS : decideLean { additive := Γₐ, linear := [] } s with
    | none => simp [decideLean, hS] at hdec
    | some ty =>
      cases ty
      case «says» p' α =>
        by_cases hp : p = p'
        · have hdec' : decideLean { additive := α :: Γₐ, linear := [] } b
                        = some φ := by
            simpa [decideLean, hS, Ctx.consA, hp] using hdec
          rw [← hp] at hS
          exact PropDeriv.letSaysE _ p α φ s b (ihS _ _ hS) (ihB _ _ hdec')
        · simp [decideLean, hS, hp] at hdec
      all_goals (simp [decideLean, hS] at hdec)
  case sfExtract m ihm =>
    intro Γₐ φ hdec
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some ty =>
      cases ty
      case «says» p_outer inner =>
        cases inner
        case speaksFor q p_inner =>
          by_cases hp : p_outer = p_inner
          · have hφ : Prop'.speaksFor q p_outer = φ := by
              simpa [decideLean, hM, hp] using hdec
            rw [← hφ]
            rw [← hp] at hM
            exact PropDeriv.sfExtractE _ p_outer q m (ihm _ _ hM)
          · simp [decideLean, hM, hp] at hdec
        all_goals (simp [decideLean, hM] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case delegate m n ihm ihn =>
    intro Γₐ φ hdec
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «says» m_p m_inner =>
        cases m_inner
        case speaksFor q_outer p_outer =>
          cases hN : decideLean { additive := Γₐ, linear := [] } n with
          | none => simp [decideLean, hM, hN] at hdec
          | some tyN =>
            cases tyN
            case «says» n_p n_inner =>
              by_cases hpp : p_outer = m_p
              · by_cases hqn : q_outer = n_p
                · have hφ : Prop'.says (Principal.acting p_outer n_p) n_inner = φ := by
                    simpa [decideLean, hM, hN, hpp, hqn] using hdec
                  rw [← hφ]
                  rw [← hpp] at hM
                  rw [hqn] at hM
                  exact PropDeriv.delegate _ p_outer n_p n_inner m n
                    (ihm _ _ hM) (ihn _ _ hN)
                · simp [decideLean, hM, hN, hpp, hqn] at hdec
              · simp [decideLean, hM, hN, hpp] at hdec
            all_goals (simp [decideLean, hM, hN] at hdec)
        all_goals (simp [decideLean, hM] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case now τ =>
    intro Γₐ φ hdec
    simp [decideLean] at hdec
    subst hdec
    exact PropDeriv.now Γₐ τ
  case attenuate m psi ihm =>
    intro Γₐ φ hdec
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «says» p phiM =>
        by_cases hψ : Prop'.beq phiM psi
        · have hphi_eq_psi : phiM = psi := Prop'.beq_eq_true_iff_eq phiM psi hψ
          have hφ : Prop'.says p psi = φ := by
            simpa [decideLean, hM, hψ] using hdec
          rw [← hφ]
          have dM := ihm Γₐ (Prop'.says p phiM) hM
          rw [hphi_eq_psi] at dM
          exact PropDeriv.attenuate _ p psi m dM
        · simp [decideLean, hM, hψ] at hdec
      all_goals (simp [decideLean, hM] at hdec)
  case liftLabel ℓ m ihm =>
    intro Γₐ φ hdec
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      have hφ : Prop'.at tyM ℓ = φ := by
        simpa [decideLean, hM] using hdec
      rw [← hφ]
      exact PropDeriv.liftLabel _ tyM ℓ m (ihm _ _ hM)
  case declassify ℓ' m π ihm ihπ =>
    intro Γₐ φ hdec
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «at» ψ _ℓ =>
        cases hπ : decideLean { additive := Γₐ, linear := [] } π with
        | none => simp [decideLean, hM, hπ] at hdec
        | some tyπ =>
          cases tyπ
          case atom n =>
            cases n with
            | zero =>
              have hφ : Prop'.at ψ ℓ' = φ := by
                simpa [decideLean, hM, hπ] using hdec
              rw [← hφ]
              exact PropDeriv.declassify _ ψ _ℓ ℓ' m π (ihm _ _ hM) (ihπ _ _ hπ)
            | succ k => simp [decideLean, hM, hπ] at hdec
          all_goals (simp [decideLean, hM, hπ] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case boxed o m n ihm ihn =>
    intro Γₐ φ hdec
    -- Same as above: fail-closed `decideLean` makes the hypothesis false.
    simp [decideLean] at hdec
  case discharge m n ihm ihn =>
    intro Γₐ φ hdec
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases tyM
      case «boxed» O inner =>
        cases hN : decideLean { additive := Γₐ, linear := [] } n with
        | none => simp [decideLean, hM, hN] at hdec
        | some tyN =>
          cases tyN
          case atom k =>
            cases k with
            | zero =>
              have hφ : inner = φ := by
                simpa [decideLean, hM, hN] using hdec
              rw [← hφ]
              exact PropDeriv.discharge _ O inner m n (ihm _ _ hM) (ihn _ _ hN)
            | succ _ => simp [decideLean, hM, hN] at hdec
          all_goals (simp [decideLean, hM, hN] at hdec)
      all_goals (simp [decideLean, hM] at hdec)
  case letTensor s b ihs ihb =>
    intro Γₐ φ hdec
    cases hS : decideLean { additive := Γₐ, linear := [] } s with
    | none => simp [decideLean, hS] at hdec
    | some tyS =>
      cases tyS
      case tensor α β =>
        have hb : decideLean { additive := α :: β :: Γₐ, linear := [] } b = some φ := by
          simpa [decideLean, hS, Ctx.consA] using hdec
        exact PropDeriv.letTensor _ α β φ s b (ihs _ _ hS) (ihb _ _ hb)
      all_goals (simp [decideLean, hS] at hdec)
  all_goals (intro Γₐ φ hdec; simp [decideLean] at hdec)

/-! ## T1 — The Decidable instance.

Combining soundness and completeness valued in `PropDeriv` gives a
Decidable instance. This is T1's headline statement, restricted to
the propositional fragment. -/

/-- T1 — propositional decidability of proof-checking. Given any
additive context, term, and proposition, decide whether a propositional
derivation exists. `noncomputable` because the witness map
`t1_propositional_soundness_prop` is `noncomputable` (Type-valued
result). -/
noncomputable instance PropDeriv.decidable_nonempty
    (Γₐ : List Prop') (M : Term) (φ : Prop') :
    Decidable (Nonempty (PropDeriv Γₐ M φ)) :=
  match h : decideLean { additive := Γₐ, linear := [] } M with
  | some ψ =>
    if hφ : Prop'.beq φ ψ = true then
      .isTrue <| by
        -- ψ = φ from beq soundness. Rewrite h's type without subst to
        -- avoid Lean's free-variable subst direction ambiguity.
        have hψ : ψ = φ := (Prop'.beq_eq_true_iff_eq φ ψ hφ).symm
        rw [hψ] at h
        exact ⟨t1_propositional_soundness_prop M Γₐ φ h⟩
    else
      .isFalse <| by
        intro ⟨d⟩
        have heq := t1_propositional_completeness Γₐ M φ d
        rw [h] at heq
        have hφψ : φ = ψ := (Option.some.inj heq).symm
        -- Substitute in hφ (the only place we need the equality);
        -- avoid `subst` whose direction over two free variables is
        -- not stable across Lean versions.
        rw [hφψ] at hφ
        exact hφ (Prop'.beq_refl _)
  | none =>
    .isFalse <| by
      intro ⟨d⟩
      have heq := t1_propositional_completeness Γₐ M φ d
      rw [h] at heq
      cases heq

/-! ## T1 — Statement form. -/

/-- T1 propositional decidability — **now proven** (via the
`PropDeriv.decidable_nonempty` instance above).

This lives in `Type` (not `Prop`), because `Decidable p` is an
inductive type with `isTrue`/`isFalse` constructors carrying proof
terms, not a propositional predicate. The universal over `Type`-sorted
arguments stays at universe `Type 0`. -/
def T1_PropositionalDecidabilityStatement : Type :=
  ∀ (Γₐ : List Prop') (M : Term) (φ : Prop'),
    Decidable (Nonempty (PropDeriv Γₐ M φ))

/-- T1 propositional decidability — discharge of the statement.
`noncomputable def` (not `theorem`) because the Decidable witness is
constructed by Type-level case analysis on `decideLean`'s output and
depends on the noncomputable `t1_propositional_soundness_prop`. -/
noncomputable def t1_propositional_decidability : T1_PropositionalDecidabilityStatement :=
  fun Γₐ M φ => PropDeriv.decidable_nonempty Γₐ M φ

/-! ## T1 — what remains OPEN (tracked in the ledger; Phase-2 scope).

Two earlier definitions here (`T1_FullCalculusDecidabilityStatement`,
`T1_ComplexityBoundStatement`) were tautological placeholders (`Γ = Γ ∧
M = M ∧ φ = φ` and `True`). They are deleted, not restated: writing the
real statements requires design work that has not been done, and a
trivially-true stand-in misrepresents the theorem's status.

Open problems:

* **Full-calculus decidability.** `PropDeriv` covers the additive
  fragment only. Decidability of `Deriv` — with linear context
  splitting on `impE`/`tensorI`/`delegate`, the modal/temporal
  constructors, and IFC labels — is unproven. Linear splitting is the
  hard part: naive search over splits is exponential, so the statement
  must come with the algorithm (input-consumption discipline or
  lazy-splitting à la Hodas-Miller), not before it.

* **Complexity bound.** The advertised `O(|M| · log |Γ|)` bound is
  unproven in any form, for any fragment. It must be stated as an
  explicit cost inequality on the Aeneas-extracted decision function
  (or a fuel-instrumented `decideLean`) — or retired from the
  marketing. Until then no `Prop` encoding of it belongs here. -/

/-! ## Sanity checks against propositional examples. -/

namespace DecidabilityChecks

/-- The polymorphic identity `λ:A. 0` has type `A ⊃ A`. Smoke-test that the
predicate `isPropositional` admits the construction. -/
example :
    (Term.lam (Prop'.atom 0) (Term.var 0)).isPropositional = true := by
  decide

/-- A `now(_)` term is propositional (it inhabits `Top` in any context,
matching the propositional fragment). -/
example :
    (Term.now { epochMs := 0 }).isPropositional = true := by
  decide

/-- `decideLean` on `now(_)` returns `some Top` regardless of context. -/
example :
    decideLean Ctx.empty (Term.now { epochMs := 0 }) = some Prop'.top := by
  rfl

/-- The polymorphic identity at atom(0) actually checks. -/
example :
    decideLean Ctx.empty
      (Term.lam (Prop'.atom 0) (Term.var 0)) =
      some (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) := by
  rfl

end DecidabilityChecks

end DLC
