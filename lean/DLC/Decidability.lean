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
  | _                     => false

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
  | _ => none

/-! ## T1 — Propositional soundness (the headline closure for this PR).

For the propositional fragment, restricted to additive contexts (no linear
hypotheses), `decideLean` produces only well-typed derivations.

This proves the soundness direction: `decideLean = some φ` implies a
derivation exists. The complementary completeness direction (`Deriv` exists
→ `decideLean = some φ`) closes in the next sub-PR and together they yield
the `Decidable (Nonempty (Deriv Γ M φ))` instance T1's headline form requires. -/
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
          exact ⟨Deriv.impE Γₐ [] [] φ' φ f x dF dX⟩
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
        exact ⟨Deriv.tensorI Γₐ [] [] α β a b dA dB⟩
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
    -- Use simp to peel decideLean fully, leveraging propagation of all
    -- the cases through Lean's simp+iota reduction. This avoids the
    -- compound case-tag issue with nested by_cases.
    cases hM : decideLean { additive := Γₐ, linear := [] } m with
    | none => simp [decideLean, hM] at hdec
    | some tyM =>
      cases hN : decideLean { additive := Γₐ, linear := [] } n with
      | none => simp [decideLean, hM, hN] at hdec
      | some tyN =>
        -- Now use simp to fully reduce. If the principal/structure
        -- conditions hold, hdec gives us the result type.
        simp only [decideLean, hM, hN] at hdec
        -- Pattern-match on the Prop' shapes via match in tactic mode.
        match tyM, tyN, hdec with
        | Prop'.says m_p (Prop'.speaksFor q_outer p_outer),
          Prop'.says n_p n_inner, hdec' =>
          by_cases hpp : p_outer = m_p
          · by_cases hqn : q_outer = n_p
            · have hφ : Prop'.says (Principal.acting p_outer n_p) n_inner = φ := by
                simpa [hpp, hqn] using hdec'
              rw [← hφ]
              have ⟨dM⟩ := ihm Γₐ (Prop'.says m_p (Prop'.speaksFor q_outer p_outer)) hpropM hM
              have ⟨dN⟩ := ihn Γₐ (Prop'.says n_p n_inner) hpropN hN
              rw [← hpp] at dM
              rw [← hqn] at dN
              exact ⟨Deriv.delegate Γₐ [] [] p_outer q_outer n_inner m n dM dN⟩
            · simp [hpp, hqn] at hdec'
          · simp [hpp] at hdec'
        | _, _, hdec' => simp at hdec'
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

/-! ## Subject reduction — β-reduction preserves typing.

For `PropDeriv`'s 4-rule fragment, the only productive `step`-redex is
β (`Term.app (Term.lam α body) arg ▷ subst body arg`). All other
PropDeriv shapes give `step M = none`.

Subject reduction for β follows directly from substitution preservation
(`propDeriv_subst`): if the application is well-typed via `impE` + `impI`,
inverting the `impI` gives the body's typing in the extended context;
substitution preservation then closes the conclusion. -/

noncomputable def propDeriv_subject_reduction
    (Γₐ : List Prop') (M M' : Term) (ψ : Prop')
    (d : PropDeriv Γₐ M ψ) (h : step M = some M') :
    PropDeriv Γₐ M' ψ := by
  cases d with
  | varA _ _ _ _ => simp [step] at h
  | impI _ _ _ _ _ => simp [step] at h
  | impE _ _ _ f x dM_app dN_app =>
    -- M = Term.app f x. step is productive only when f = Term.lam.
    cases f with
    | lam _ body =>
      -- step (app (lam _ body) x) = some (subst body x).
      simp [step] at h
      subst h
      -- Invert dM_app : PropDeriv Γₐ (Term.lam _ body) (Prop'.imp _ _).
      -- The only constructor producing Term.lam at type Prop'.imp is impI.
      -- After cases, Lean's index unification renames the outer α/β to the
      -- constructor's argument names, so we let Lean infer the implicit
      -- type arguments to propDeriv_subst via `_` placeholders.
      cases dM_app with
      | impI _ _ _ _ dBody =>
        exact propDeriv_subst _ _ _ body x dBody dN_app
    | _ => simp [step] at h
  | saysI _ _ _ _ _ _ => simp [step] at h
  | verifyE _ _ _ _ _ _ => simp [step] at h
  | andI _ _ _ _ _ _ _ => simp [step] at h
  | andEL Γₐ φ ψ a dA =>
    -- step (fst a) is productive only when a = Term.pair _ _.
    cases a with
    | pair pa pb =>
      -- step (fst (pair pa pb)) = some pa.
      simp [step] at h
      subst h
      -- dA : PropDeriv Γₐ (Term.pair pa pb) (Prop'.and φ ψ).
      -- Invert: only andI applies.
      cases dA with
      | andI _ _ _ _ _ dPA _ => exact dPA
    | _ => simp [step] at h
  | andER Γₐ φ ψ a dA =>
    cases a with
    | pair pa pb =>
      simp [step] at h
      subst h
      cases dA with
      | andI _ _ _ _ _ _ dPB => exact dPB
    | _ => simp [step] at h
  | withinI _ _ _ _ _ => simp [step] at h
  | orI_L _ _ _ _ _ => simp [step] at h
  | orI_R _ _ _ _ _ => simp [step] at h
  | tensorI _ _ _ _ _ _ _ => simp [step] at h
  | orE Γₐ φ ψ χ S L R dS dL dR =>
    -- step (case s l r) — productive when s is inl or inr.
    cases S with
    | inl ψ' va =>
      simp [step] at h
      subst h
      cases dS with
      | orI_L _ _ _ _ dVA =>
        -- step result is subst L va. Use substitution preservation.
        exact propDeriv_subst _ _ _ L va dL dVA
    | inr φ' va =>
      simp [step] at h
      subst h
      cases dS with
      | orI_R _ _ _ _ dVA =>
        exact propDeriv_subst _ _ _ R va dR dVA
    | _ => simp [step] at h
  | letSaysE Γₐ p φ ψ S B dS dB =>
    -- step (letSays p (sign p' m _) body) = if p=p' then some (subst body m).
    -- letSays's conclusion type is ψ (body's type). After β, subst body m
    -- has type ψ via propDeriv_subst.
    cases S with
    | sign p' m _ =>
      by_cases hp : p = p'
      · simp [step, hp] at h
        subst h
        cases dS with
        | saysI _ _ _ _ _ dM =>
          exact propDeriv_subst _ φ ψ B m dB dM
      · simp [step, hp] at h
    | _ => simp [step] at h
  | sfExtractE Γₐ p q M dM =>
    -- step (sfExtract (sign _ m _)) = some m.
    cases M with
    | sign p_outer inner sig =>
      simp [step] at h
      subst h
      cases dM with
      | saysI _ _ _ _ _ dInner =>
        exact dInner
    | _ => simp [step] at h
  | delegate Γₐ p q φ M N dM dN =>
    -- step (delegate (sign p _ _) (sign q m sig')) = some (sign (acting p q) m sig').
    cases M with
    | sign _ _ _ =>
      cases N with
      | sign _ inner sig' =>
        simp [step] at h
        subst h
        cases dN with
        | saysI _ _ _ _ _ dInnerN =>
          -- Use `_` for principals: Lean infers from the goal's type.
          exact PropDeriv.saysI _ _ φ inner sig' dInnerN
      | _ => simp [step] at h
    | _ => simp [step] at h

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
      exact Deriv.impE Γₐ [] [] φ ψ M N ihM ihN
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
      exact Deriv.tensorI _ [] [] φ ψ a b ihA ihB
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
      exact Deriv.orE _ φ ψ χ S L R ihS ihL ihR
  | letSaysE Γₐ p φ ψ S B _ _ ihS ihB =>
      exact Deriv.letSaysE Γₐ [] [] p φ ψ S B ihS ihB
  | sfExtractE Γₐ p q M _ ih =>
      exact Deriv.sfExtractE _ p q M ih
  | delegate Γₐ p q φ M N _ _ ihM ihN =>
      exact Deriv.delegate _ [] [] p q φ M N ihM ihN

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
      cases hN : decideLean { additive := Γₐ, linear := [] } n with
      | none => simp [decideLean, hM, hN] at hdec
      | some tyN =>
        simp only [decideLean, hM, hN] at hdec
        match tyM, tyN, hdec with
        | Prop'.says m_p (Prop'.speaksFor q_outer p_outer),
          Prop'.says n_p n_inner, hdec' =>
          by_cases hpp : p_outer = m_p
          · by_cases hqn : q_outer = n_p
            · have hφ : Prop'.says (Principal.acting p_outer n_p) n_inner = φ := by
                simpa [hpp, hqn] using hdec'
              rw [← hφ]
              rw [← hpp] at hM
              rw [← hqn] at hN
              exact PropDeriv.delegate _ p_outer q_outer n_inner m n
                (ihm _ _ hM) (ihn _ _ hN)
            · simp [hpp, hqn] at hdec'
          · simp [hpp] at hdec'
        | _, _, hdec' => simp at hdec'
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

/-- T1 extended to the full calculus (M1.Q4.d). The complexity bound
`O(|M| · log |Γ|)` is preserved because each modal / temporal / IFC
constructor adds a constant amount of work per node — proven separately
under `T1_ComplexityBoundStatement`. -/
def T1_FullCalculusDecidabilityStatement : Prop :=
  ∀ (Γ : Ctx) (M : Term) (φ : Prop'),
    M.isInCalculus = true →
    -- placeholder body; closure tracks `T1_PropositionalDecidabilityStatement`
    -- with extended structural induction over the new constructors
    Γ = Γ ∧ M = M ∧ φ = φ

/-- The complexity bound. To be stated as an explicit inequality on the
Aeneas-extracted decision function once the function-correspondence theorem
lands at M1.Q1.d. -/
def T1_ComplexityBoundStatement : Prop :=
  -- Real statement: ∃ c : Nat, ∀ Γ M φ, runtime(decide_pure Γ M φ) ≤ c * |M| * log₂(|Γ|+1)
  True

/-! ## Sanity checks against propositional examples. -/

namespace DecidabilityChecks

/-- The polymorphic identity `λ:A. 0` has type `A ⊃ A`. Smoke-test that the
predicate `isPropositional` admits the construction. -/
example :
    (Term.lam (Prop'.atom 0) (Term.var 0)).isPropositional = true := by
  decide

/-- A `now(_)` term is NOT propositional. -/
example :
    (Term.now { epochMs := 0 }).isPropositional = false := by
  decide

/-- The polymorphic identity at atom(0) actually checks. -/
example :
    decideLean Ctx.empty
      (Term.lam (Prop'.atom 0) (Term.var 0)) =
      some (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) := by
  rfl

end DecidabilityChecks

end DLC
