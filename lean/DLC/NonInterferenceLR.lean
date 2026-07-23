/-
T3 rung 3b — the redesigned two-run logical relation.

Design: `spec/t3-two-run-design-2026-07.md`. This relation replaces
`Indistinguishable` (which cannot carry a fundamental lemma: its
product cases were non-projective and its arrows diagonal) for the
purposes of the real T3. It is defined over the congruent,
deterministic reduction of `DLC.Reduce` (rung 3b-0) and the
`Steps`/`Joinable` metatheory of `DLC.ReduceMeta` (rung 2).

Shape, by connective:
* atoms / speaksFor — `Joinable` (equality up to computation);
* `at φ ℓ` — observability gate, then VALUE-STYLE: both sides reduce
  to `liftLabel ℓ` wrappers with related payloads;
* `says p φ`, `within τ φ`, `tensor`, `or` — value-style: both sides
  reduce to the introduction form (same principal / same side) with
  related components;
* `and φ ψ` — PROJECTIVE: the projections are related. Congruence
  (rung 3b-0) is what makes projections of non-value terms evaluate;
* `imp` / `lolli` — genuinely BINARY arrows over CLOSED related
  arguments (the closed-LR formulation: the fundamental lemma's
  binder cases commute substitutions past the environment via
  `msubstAt_substAt_comm`, which requires the placed argument
  closed);
* `top` — trivial; `bot`, `boxed O φ` — trivially `True`
  (uninhabited-in-fragment types: no observation is possible).

  CAVEAT ADDED 2026-07-20 (T4 ladder R5). The `boxed` justification is
  still correct but is now load-bearing in a way it was not before, and
  the next person to extend T3 must not skip past it.

  `LRel ℓLow (.boxed O φ) M N = True` says T3 relates ANY two terms at an
  obligation-carrying type. That is sound here only because
  `Prop'.boxed` is uninhabited in THIS fragment: `PropDeriv` has no rule
  introducing a term at a boxed type (it appears solely as the premise of
  `PropDeriv.discharge`). So the trivial case is unreachable, not
  permissive.

  That changes the moment T3 extends to the full `Deriv` judgment, which
  DOES have `boxI` — and as of R1–R5 there is now a term constructor,
  `Term.boxed`, that inhabits it. At that point `True` stops being
  "unreachable" and becomes "T3 makes no claim about obligation-carrying
  propositions", which is a genuine hole in the theorem rather than an
  economy in the definition.

  Extending T3 to `Deriv` (T3's own remaining open item, and roadmap
  item 3) therefore requires giving `.boxed` a real clause — plausibly
  the `at`/`says` shape: both sides must step to `Term.boxed` with the
  same obligation and `LRel`-related payloads. Do not lift the
  fragment without doing so.

THE RELATION IS A PER, NOT REFLEXIVE. `LRel ℓLow φ M M` fails for,
e.g., a stuck non-sign term at a `says` type — by design: reflexivity
restricted to well-typed terms IS the fundamental lemma (rung 3c).
This file proves the PER structure (symm, trans — transitivity of the
arrow case via the standard PER trick), anti-reduction closure, and
the `Steps`-congruence lifting lemmas the fundamental lemma will use.
-/

import DLC.ReduceMeta
import DLC.Progress
import DLC.NonInterferenceTwoRun
import DLC.IFCLabel

namespace DLC

/-! ## The relation -/

/-- The two-run logical relation at observer label `ℓLow`. See the
module docstring for the design rationale per connective. -/
def LRel (ℓLow : Label) : Prop' → Term → Term → Prop
  | .top, _, _ => True
  | .bot, _, _ => True
  | .atom _, M, N => Joinable M N
  | .speaksFor _ _, M, N => Joinable M N
  | .at φ ℓ, M, N =>
      if Label.le ℓ ℓLow then
        ∃ m₁ m₂, Steps M (Term.liftLabel ℓ m₁) ∧ Steps N (Term.liftLabel ℓ m₂) ∧
          LRel ℓLow φ m₁ m₂
      else True
  | .says p φ, M, N =>
      ∃ m₁ σ₁ m₂ σ₂, Steps M (Term.sign p m₁ σ₁) ∧ Steps N (Term.sign p m₂ σ₂) ∧
        LRel ℓLow φ m₁ m₂
  | .within τ φ, M, N =>
      ∃ m₁ m₂, Steps M (Term.withinIntro τ m₁) ∧ Steps N (Term.withinIntro τ m₂) ∧
        LRel ℓLow φ m₁ m₂
  | .boxed _ _, _, _ => True
  | .and φ ψ, M, N =>
      LRel ℓLow φ (Term.fst M) (Term.fst N) ∧
      LRel ℓLow ψ (Term.snd M) (Term.snd N)
  | .or φ ψ, M, N =>
      (∃ χ₁ χ₂ a₁ a₂, Steps M (Term.inl χ₁ a₁) ∧ Steps N (Term.inl χ₂ a₂) ∧
        LRel ℓLow φ a₁ a₂) ∨
      (∃ χ₁ χ₂ a₁ a₂, Steps M (Term.inr χ₁ a₁) ∧ Steps N (Term.inr χ₂ a₂) ∧
        LRel ℓLow ψ a₁ a₂)
  | .tensor φ ψ, M, N =>
      ∃ a₁ b₁ a₂ b₂, Steps M (Term.tensorIntro a₁ b₁) ∧
        Steps N (Term.tensorIntro a₂ b₂) ∧
        LRel ℓLow φ a₁ a₂ ∧ LRel ℓLow ψ b₁ b₂
  | .imp φ ψ, M, N =>
      ∀ X Y, Closed X → Closed Y → LRel ℓLow φ X Y →
        LRel ℓLow ψ (Term.app M X) (Term.app N Y)
  | .lolli φ ψ, M, N =>
      ∀ X Y, Closed X → Closed Y → LRel ℓLow φ X Y →
        LRel ℓLow ψ (Term.app M X) (Term.app N Y)
  | .replicated φ, M, N =>
      -- COLLAPSING definition (design §5.2): a replicated value is two-run
      -- related iff its underlying `φ` is — convergence collapses replicas to
      -- one observable, so the modality is transparent to the low observer.
      -- Every PER/anti-reduction/congruence lemma re-founds through the single
      -- IH. (Inert this increment: `replicated` is untypable, never arises.)
      LRel ℓLow φ M N

/-! ## Values are inert -/

/-- Values do not step. -/
theorem value_no_step {V : Term} (hv : Value V) : step V = none := by
  cases V <;> first | rfl | exact absurd hv (by simp [Value])

/-- Multi-step reduction from a value goes nowhere. -/
theorem value_steps_eq {V W : Term} (hv : Value V) (h : Steps V W) : W = V := by
  cases h with
  | refl _ => rfl
  | head hstep _ => rw [value_no_step hv] at hstep; cases hstep

/-- Two reduction paths from one term ending in VALUES end in the SAME
value — determinism's payoff, via semi-confluence. -/
theorem steps_to_value_unique {M V₁ V₂ : Term}
    (h₁ : Steps M V₁) (h₂ : Steps M V₂)
    (hv₁ : Value V₁) (hv₂ : Value V₂) : V₁ = V₂ := by
  rcases steps_semiconfluent h₁ h₂ with h | h
  · exact (value_steps_eq hv₁ h).symm
  · exact value_steps_eq hv₂ h

/-! ## ξ-congruence: single steps and `Steps` lift through elimination
positions.

For each elimination form, a stepping scrutinee/function lifts to a
step of the whole form: the scrutinee cannot be the redex value shape
(values do not step), so the congruence branch of `step` fires. -/

theorem step_app_congr {f f' x : Term} (h : step f = some f') :
    step (Term.app f x) = some (Term.app f' x) := by
  cases f <;> simp_all [step]

theorem step_fst_congr {m m' : Term} (h : step m = some m') :
    step (Term.fst m) = some (Term.fst m') := by
  cases m <;> simp_all [step]

theorem step_snd_congr {m m' : Term} (h : step m = some m') :
    step (Term.snd m) = some (Term.snd m') := by
  cases m <;> simp_all [step]

theorem step_case_congr {s s' l r : Term} (h : step s = some s') :
    step (Term.case s l r) = some (Term.case s' l r) := by
  cases s <;> simp_all [step]

theorem step_letTensor_congr {s s' b : Term} (h : step s = some s') :
    step (Term.letTensor s b) = some (Term.letTensor s' b) := by
  cases s <;> simp_all [step]

theorem step_letSays_congr {p : Principal} {s s' b : Term}
    (h : step s = some s') :
    step (Term.letSays p s b) = some (Term.letSays p s' b) := by
  cases s <;> simp_all [step]

theorem step_sfExtract_congr {m m' : Term} (h : step m = some m') :
    step (Term.sfExtract m) = some (Term.sfExtract m') := by
  cases m <;> simp_all [step]

theorem step_delegate_left_congr {m m' n : Term} (h : step m = some m') :
    step (Term.delegate m n) = some (Term.delegate m' n) := by
  cases m <;> simp_all [step]

theorem step_delegate_right_congr {p : Principal} {mi : Term}
    {si : Signature} {n n' : Term} (h : step n = some n') :
    step (Term.delegate (Term.sign p mi si) n)
      = some (Term.delegate (Term.sign p mi si) n') := by
  cases n <;> simp_all [step]

/-- Lift a `Steps` path through a congruence position. Parameterized by
the single-step lifting to avoid nine copies of the same induction. -/
theorem steps_congr {F : Term → Term}
    (lift : ∀ {a a' : Term}, step a = some a' → step (F a) = some (F a'))
    {m m' : Term} (h : Steps m m') : Steps (F m) (F m') := by
  induction h with
  | refl _ => exact .refl _
  | head hstep _ ih => exact .head (lift hstep) ih

/-! ## Anti-reduction (head expansion) -/

/-- The relation is closed under expansion on the LEFT: if `M` steps to
`M'` and `M'` is related to `N`, so is `M`. Induction on the
proposition; `Joinable`/value-style cases prepend the step, the
projective `and` case and the arrows lift the step through
`fst`/`snd`/`app` congruence. -/
theorem lrel_expand_left (ℓLow : Label) :
    ∀ (φ : Prop') {M M' N : Term}, step M = some M' →
      LRel ℓLow φ M' N → LRel ℓLow φ M N := by
  intro φ
  induction φ with
  | top => intro M M' N _ _; trivial
  | bot => intro M M' N _ _; trivial
  | atom n =>
      intro M M' N h hr
      obtain ⟨V, hM, hN⟩ := hr
      exact ⟨V, .head h hM, hN⟩
  | speaksFor p q =>
      intro M M' N h hr
      obtain ⟨V, hM, hN⟩ := hr
      exact ⟨V, .head h hM, hN⟩
  | «at» φ ℓ ih =>
      intro M M' N h hr
      simp only [LRel] at hr ⊢
      split at hr <;> rename_i hle
      · rw [if_pos hle]
        obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
        exact ⟨m₁, m₂, .head h hM, hN, hp⟩
      · rw [if_neg hle]; trivial
  | «says» p φ ih =>
      intro M M' N h hr
      obtain ⟨m₁, σ₁, m₂, σ₂, hM, hN, hp⟩ := hr
      exact ⟨m₁, σ₁, m₂, σ₂, .head h hM, hN, hp⟩
  | within τ φ ih =>
      intro M M' N h hr
      obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
      exact ⟨m₁, m₂, .head h hM, hN, hp⟩
  | boxed O φ ih => intro M M' N _ _; trivial
  | and φ ψ ihφ ihψ =>
      intro M M' N h hr
      exact ⟨ihφ (step_fst_congr h) hr.1, ihψ (step_snd_congr h) hr.2⟩
  | or φ ψ ihφ ihψ =>
      intro M M' N h hr
      rcases hr with ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩ | ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩
      · exact .inl ⟨χ₁, χ₂, a₁, a₂, .head h hM, hN, hp⟩
      · exact .inr ⟨χ₁, χ₂, a₁, a₂, .head h hM, hN, hp⟩
  | tensor φ ψ ihφ ihψ =>
      intro M M' N h hr
      obtain ⟨a₁, b₁, a₂, b₂, hM, hN, hp, hq⟩ := hr
      exact ⟨a₁, b₁, a₂, b₂, .head h hM, hN, hp, hq⟩
  | imp φ ψ ihφ ihψ =>
      intro M M' N h hr X Y hX hY hXY
      exact ihψ (step_app_congr h) (hr X Y hX hY hXY)
  | lolli φ ψ ihφ ihψ =>
      intro M M' N h hr X Y hX hY hXY
      exact ihψ (step_app_congr h) (hr X Y hX hY hXY)
  | replicated φ ih =>
      -- collapsing def: LRel at `replicated φ` is defeq LRel at `φ`.
      intro M M' N h hr
      exact ih h hr

/-- Right-side expansion, by the same argument. -/
theorem lrel_expand_right (ℓLow : Label) :
    ∀ (φ : Prop') {M N N' : Term}, step N = some N' →
      LRel ℓLow φ M N' → LRel ℓLow φ M N := by
  intro φ
  induction φ with
  | top => intro M N N' _ _; trivial
  | bot => intro M N N' _ _; trivial
  | atom n =>
      intro M N N' h hr
      obtain ⟨V, hM, hN⟩ := hr
      exact ⟨V, hM, .head h hN⟩
  | speaksFor p q =>
      intro M N N' h hr
      obtain ⟨V, hM, hN⟩ := hr
      exact ⟨V, hM, .head h hN⟩
  | «at» φ ℓ ih =>
      intro M N N' h hr
      simp only [LRel] at hr ⊢
      split at hr <;> rename_i hle
      · rw [if_pos hle]
        obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
        exact ⟨m₁, m₂, hM, .head h hN, hp⟩
      · rw [if_neg hle]; trivial
  | «says» p φ ih =>
      intro M N N' h hr
      obtain ⟨m₁, σ₁, m₂, σ₂, hM, hN, hp⟩ := hr
      exact ⟨m₁, σ₁, m₂, σ₂, hM, .head h hN, hp⟩
  | within τ φ ih =>
      intro M N N' h hr
      obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
      exact ⟨m₁, m₂, hM, .head h hN, hp⟩
  | boxed O φ ih => intro M N N' _ _; trivial
  | and φ ψ ihφ ihψ =>
      intro M N N' h hr
      exact ⟨ihφ (step_fst_congr h) hr.1, ihψ (step_snd_congr h) hr.2⟩
  | or φ ψ ihφ ihψ =>
      intro M N N' h hr
      rcases hr with ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩ | ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩
      · exact .inl ⟨χ₁, χ₂, a₁, a₂, hM, .head h hN, hp⟩
      · exact .inr ⟨χ₁, χ₂, a₁, a₂, hM, .head h hN, hp⟩
  | tensor φ ψ ihφ ihψ =>
      intro M N N' h hr
      obtain ⟨a₁, b₁, a₂, b₂, hM, hN, hp, hq⟩ := hr
      exact ⟨a₁, b₁, a₂, b₂, hM, .head h hN, hp, hq⟩
  | imp φ ψ ihφ ihψ =>
      intro M N N' h hr X Y hX hY hXY
      exact ihψ (step_app_congr h) (hr X Y hX hY hXY)
  | lolli φ ψ ihφ ihψ =>
      intro M N N' h hr X Y hX hY hXY
      exact ihψ (step_app_congr h) (hr X Y hX hY hXY)
  | replicated φ ih =>
      intro M N N' h hr
      exact ih h hr

/-- Multi-step expansion on the left. -/
theorem lrel_expand_steps_left (ℓLow : Label) (φ : Prop') {M M' N : Term}
    (hM : Steps M M') (hr : LRel ℓLow φ M' N) : LRel ℓLow φ M N := by
  induction hM with
  | refl _ => exact hr
  | head h _ ih => exact lrel_expand_left ℓLow φ h (ih hr)

/-- Multi-step expansion on the right. -/
theorem lrel_expand_steps_right (ℓLow : Label) (φ : Prop') {M N N' : Term}
    (hN : Steps N N') (hr : LRel ℓLow φ M N') : LRel ℓLow φ M N := by
  induction hN with
  | refl _ => exact hr
  | head h _ ih => exact lrel_expand_right ℓLow φ h (ih hr)

/-- Multi-step expansion on both sides. -/
theorem lrel_expand (ℓLow : Label) (φ : Prop') {M M' N N' : Term}
    (hM : Steps M M') (hN : Steps N N')
    (hr : LRel ℓLow φ M' N') : LRel ℓLow φ M N :=
  lrel_expand_steps_left ℓLow φ hM (lrel_expand_steps_right ℓLow φ hN hr)

/-! ## PER structure -/

/-- Symmetry. -/
theorem lrel_symm (ℓLow : Label) :
    ∀ (φ : Prop') {M N : Term}, LRel ℓLow φ M N → LRel ℓLow φ N M := by
  intro φ
  induction φ with
  | top => intro M N _; trivial
  | bot => intro M N _; trivial
  | atom n => intro M N h; exact h.symm
  | speaksFor p q => intro M N h; exact h.symm
  | «at» φ ℓ ih =>
      intro M N hr
      simp only [LRel] at hr ⊢
      split at hr <;> rename_i hle
      · rw [if_pos hle]
        obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
        exact ⟨m₂, m₁, hN, hM, ih hp⟩
      · rw [if_neg hle]; trivial
  | «says» p φ ih =>
      intro M N hr
      obtain ⟨m₁, σ₁, m₂, σ₂, hM, hN, hp⟩ := hr
      exact ⟨m₂, σ₂, m₁, σ₁, hN, hM, ih hp⟩
  | within τ φ ih =>
      intro M N hr
      obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
      exact ⟨m₂, m₁, hN, hM, ih hp⟩
  | boxed O φ ih => intro M N _; trivial
  | and φ ψ ihφ ihψ =>
      intro M N hr
      exact ⟨ihφ hr.1, ihψ hr.2⟩
  | or φ ψ ihφ ihψ =>
      intro M N hr
      rcases hr with ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩ | ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩
      · exact .inl ⟨χ₂, χ₁, a₂, a₁, hN, hM, ihφ hp⟩
      · exact .inr ⟨χ₂, χ₁, a₂, a₁, hN, hM, ihψ hp⟩
  | tensor φ ψ ihφ ihψ =>
      intro M N hr
      obtain ⟨a₁, b₁, a₂, b₂, hM, hN, hp, hq⟩ := hr
      exact ⟨a₂, b₂, a₁, b₁, hN, hM, ihφ hp, ihψ hq⟩
  | imp φ ψ ihφ ihψ =>
      intro M N hr X Y hX hY hXY
      exact ihψ (hr Y X hY hX (ihφ hXY))
  | lolli φ ψ ihφ ihψ =>
      intro M N hr X Y hX hY hXY
      exact ihψ (hr Y X hY hX (ihφ hXY))
  | replicated φ ih =>
      intro M N hr
      exact ih hr

/-- Transitivity. The value-style cases use determinism
(`steps_to_value_unique`) to identify the two reducts of the middle
term; the arrow cases use the standard PER composition: from
`LRel φ X Y` derive `LRel φ Y Y` (symm + the φ-IH), feed it to the
second function, and chain at ψ. -/
theorem lrel_trans (ℓLow : Label) :
    ∀ (φ : Prop') {M N P : Term},
      LRel ℓLow φ M N → LRel ℓLow φ N P → LRel ℓLow φ M P := by
  intro φ
  induction φ with
  | top => intro M N P _ _; trivial
  | bot => intro M N P _ _; trivial
  | atom n => intro M N P h₁ h₂; exact h₁.trans h₂
  | speaksFor p q => intro M N P h₁ h₂; exact h₁.trans h₂
  | «at» φ ℓ ih =>
      intro M N P h₁ h₂
      simp only [LRel] at h₁ h₂ ⊢
      split at h₁ <;> rename_i hle
      · rw [if_pos hle] at h₂ ⊢
        obtain ⟨m₁, m₂, hM, hN₁, hp₁⟩ := h₁
        obtain ⟨n₁, n₂, hN₂, hP, hp₂⟩ := h₂
        have heq : Term.liftLabel ℓ m₂ = Term.liftLabel ℓ n₁ :=
          steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value])
        cases heq
        exact ⟨m₁, n₂, hM, hP, ih hp₁ hp₂⟩
      · rw [if_neg hle]; trivial
  | «says» p φ ih =>
      intro M N P h₁ h₂
      obtain ⟨m₁, σ₁, m₂, σ₂, hM, hN₁, hp₁⟩ := h₁
      obtain ⟨n₁, τ₁, n₂, τ₂, hN₂, hP, hp₂⟩ := h₂
      have heq : Term.sign p m₂ σ₂ = Term.sign p n₁ τ₁ :=
        steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value])
      cases heq
      exact ⟨m₁, σ₁, n₂, τ₂, hM, hP, ih hp₁ hp₂⟩
  | within τ φ ih =>
      intro M N P h₁ h₂
      obtain ⟨m₁, m₂, hM, hN₁, hp₁⟩ := h₁
      obtain ⟨n₁, n₂, hN₂, hP, hp₂⟩ := h₂
      have heq : Term.withinIntro τ m₂ = Term.withinIntro τ n₁ :=
        steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value])
      cases heq
      exact ⟨m₁, n₂, hM, hP, ih hp₁ hp₂⟩
  | boxed O φ ih => intro M N P _ _; trivial
  | and φ ψ ihφ ihψ =>
      intro M N P h₁ h₂
      exact ⟨ihφ h₁.1 h₂.1, ihψ h₁.2 h₂.2⟩
  | or φ ψ ihφ ihψ =>
      intro M N P h₁ h₂
      rcases h₁ with ⟨χ₁, χ₂, a₁, a₂, hM, hN₁, hp₁⟩ | ⟨χ₁, χ₂, a₁, a₂, hM, hN₁, hp₁⟩ <;>
        rcases h₂ with ⟨χ₃, χ₄, b₁, b₂, hN₂, hP, hp₂⟩ | ⟨χ₃, χ₄, b₁, b₂, hN₂, hP, hp₂⟩
      · have heq : Term.inl χ₂ a₂ = Term.inl χ₃ b₁ :=
          steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value])
        cases heq
        exact .inl ⟨χ₁, χ₄, a₁, b₂, hM, hP, ihφ hp₁ hp₂⟩
      · exact absurd
          (steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value]))
          (by simp)
      · exact absurd
          (steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value]))
          (by simp)
      · have heq : Term.inr χ₂ a₂ = Term.inr χ₃ b₁ :=
          steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value])
        cases heq
        exact .inr ⟨χ₁, χ₄, a₁, b₂, hM, hP, ihψ hp₁ hp₂⟩
  | tensor φ ψ ihφ ihψ =>
      intro M N P h₁ h₂
      obtain ⟨a₁, b₁, a₂, b₂, hM, hN₁, hp₁, hq₁⟩ := h₁
      obtain ⟨c₁, d₁, c₂, d₂, hN₂, hP, hp₂, hq₂⟩ := h₂
      have heq : Term.tensorIntro a₂ b₂ = Term.tensorIntro c₁ d₁ :=
        steps_to_value_unique hN₁ hN₂ (by simp [Value]) (by simp [Value])
      cases heq
      exact ⟨a₁, b₁, c₂, d₂, hM, hP, ihφ hp₁ hp₂, ihψ hq₁ hq₂⟩
  | imp φ ψ ihφ ihψ =>
      intro M N P h₁ h₂ X Y hX hY hXY
      have hYY : LRel ℓLow φ Y Y := ihφ (lrel_symm ℓLow φ hXY) hXY
      exact ihψ (h₁ X Y hX hY hXY) (h₂ Y Y hY hY hYY)
  | lolli φ ψ ihφ ihψ =>
      intro M N P h₁ h₂ X Y hX hY hXY
      have hYY : LRel ℓLow φ Y Y := ihφ (lrel_symm ℓLow φ hXY) hXY
      exact ihψ (h₁ X Y hX hY hXY) (h₂ Y Y hY hY hYY)
  | replicated φ ih =>
      intro M N P h₁ h₂
      exact ih h₁ h₂


/-! ## Design witnesses.

The two claims that distinguish this relation from the retired
reflexivity-based one, machine-checked. -/

namespace LRelChecks

/-- NOT REFLEXIVE on stuck terms at value-style types: a bare variable
is never related to itself at a `says` type, because it reduces to no
`sign` value. Reflexivity restricted to well-typed terms is exactly
the fundamental lemma (rung 3c) — it cannot come for free. -/
example (ℓ : Label) (p : Principal) :
    ¬ LRel ℓ (Prop'.says p Prop'.top) (Term.var 0) (Term.var 0) := by
  rintro ⟨m₁, σ₁, m₂, σ₂, hM, -, -⟩
  cases hM with
  | head hstep _ => cases hstep

/-- Computation is respected: `fst ⟨x₃, x₄⟩` is related to `x₃` at an
atom — equality up to reduction, not syntactic equality. -/
example (ℓ : Label) :
    LRel ℓ (Prop'.atom 0)
      (Term.fst (Term.pair (Term.var 3) (Term.var 4))) (Term.var 3) :=
  ⟨Term.var 3, Steps.single rfl, .refl _⟩

end LRelChecks

end DLC
