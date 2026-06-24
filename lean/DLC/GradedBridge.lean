/-
DLC — the graded natural transformation τ : Graded⟨RiskGrade⟩ ⇒ Graded⟨DpBudget⟩.

CT-unification proof #3 (the moonshot — the only unification on the roadmap that
CANNOT be replaced by a runtime check). It bridges two *different* gradings over
the same category:

  * `RiskGrade` — composes by JOIN (⊔, a bounded join-semilattice): risk can only
    rise along a workflow. This is the nucleus risk monad's grade
    (`portcullis/src/graded.rs`, `RiskGrade`/`StateRisk`).
  * `DpBudget` — composes by ADD (⊕, saturating): differential-privacy budget can
    only deplete. This is DLC's existing graded comonad (`DLC/Graded.lean`).

τ maps the join-grade to the additive-grade *lax-monoidally*:
    τ(g₁ ⊔ g₂)  ≤  τ(g₁) ⊕ τ(g₂)
which is the coherence that makes "this agent at risk level r gets DP budget τ(r)"
a sound, composable policy — the formal foundation for risk-adaptive differential
privacy in workstream-kg.

Honest scope (model-level): `RiskGrade` lives in Rust (`portcullis/graded.rs`,
property-tested) and `workstream-kg`; Aeneas cannot extract its bool/enum shape, so
this proves the MODEL, connected to the Rust enum by structural parity (discriminants
0..2), not the running bytes. The lax-monoidal coherence and `pure`/`consume`
preservation are proven here by `decide`/`rfl`; the full strong-naturality square
over arbitrary continuations is stated as the remaining goal (no `sorry`).

Reuses `DLC/Graded.lean` (DpBudget, saturatingAdd, le) verbatim.
-/

import DLC.Graded

namespace DLC

/-! ## The join-graded side: RiskGrade -/

/-- A risk grade. Composes by `join` (least-upper-bound): sequential steps can only
get riskier. Mirrors `portcullis::graded::RiskGrade`. -/
inductive RiskGrade where
  | low | medium | high
  deriving Repr, DecidableEq, Fintype

namespace RiskGrade

/-- Rank for the chain order. -/
def rank : RiskGrade → Nat
  | low => 0 | medium => 1 | high => 2

/-- Bottom = `low` (no risk). Identity for `join`. -/
def bottom : RiskGrade := low

/-- Join = the riskier of the two (least upper bound). -/
def join (a b : RiskGrade) : RiskGrade := if a.rank ≤ b.rank then b else a

theorem join_comm (a b : RiskGrade) : join a b = join b a := by decide
theorem join_assoc (a b c : RiskGrade) : join (join a b) c = join a (join b c) := by decide
theorem join_idem (a : RiskGrade) : join a a = a := by decide
theorem join_bottom_left (a : RiskGrade) : join bottom a = a := by decide

end RiskGrade

/-! ## The grade map τ on grades

A concrete, monotone assignment of DP budget to risk level (micro-units). The
exact numbers are policy; what matters is monotonicity + the lax-monoidal law,
both kernel-checked below. -/

/-- τ on grades: risk level ↦ DP budget. Monotone; `low ↦ 0`. -/
def riskToBudget : RiskGrade → DpBudget
  | .low => ⟨0, 0⟩
  | .medium => ⟨500000, 1⟩
  | .high => ⟨1000000, 1000⟩

/-- τ sends the risk bottom to the budget zero (units align). -/
theorem riskToBudget_bottom : riskToBudget RiskGrade.bottom = DpBudget.zero := rfl

/-- τ is monotone: riskier ⇒ at least as much budget consumed. -/
theorem riskToBudget_mono (a b : RiskGrade) :
    a.rank ≤ b.rank → (riskToBudget a).le (riskToBudget b) = true := by decide

/-- **The lax-monoidal coherence** — the heart of the bridge:
`τ(a ⊔ b) ≤ τ(a) ⊕ τ(b)`. Join-grade composition is dominated by additive-grade
composition, so collapsing a risk join into a budget sum is always sound (never
under-charges). Kernel-checked by `decide` over the finite grade pairs. -/
theorem riskToBudget_lax_monoidal (a b : RiskGrade) :
    (riskToBudget (RiskGrade.join a b)).le
      ((riskToBudget a).saturatingAdd (riskToBudget b)) = true := by decide

/-! ## τ on the graded carriers (the monad morphism)

`RGraded` is the risk-graded carrier (value + risk grade). τ transports it to
DLC's DP-budget `Graded`. We prove the value is preserved and `pure`/`consume`
are respected lax-monoidally. -/

/-- The risk-graded carrier: a value paired with its risk grade. -/
structure RGraded (α : Type) where
  value : α
  grade : RiskGrade
  deriving Repr

namespace RGraded

/-- Inject at the risk bottom (`low`). -/
def pure {α : Type} (a : α) : RGraded α := ⟨a, RiskGrade.bottom⟩

/-- Functor action. -/
def map {α β : Type} (f : α → β) (g : RGraded α) : RGraded β := ⟨f g.value, g.grade⟩

/-- Sequence: a risk step composes by JOIN (risk rises). -/
def consume {α : Type} (g : RGraded α) (extra : RiskGrade) : RGraded α :=
  ⟨g.value, g.grade.join extra⟩

end RGraded

/-- The natural transformation τ on carriers: keep the value, map the grade. -/
def tau {α : Type} (g : RGraded α) : Graded α :=
  ⟨g.value, riskToBudget g.grade⟩

/-- τ preserves the underlying value (the natural-transformation component is
identity on values). -/
@[simp] theorem tau_value {α : Type} (g : RGraded α) : (tau g).value = g.value := rfl

/-- τ respects `pure`: `τ (pure a) = pure a`. (Unit preservation — half of the
monad-morphism laws.) -/
theorem tau_pure {α : Type} (a : α) : tau (RGraded.pure a) = Graded.pure a := by
  simp [tau, RGraded.pure, Graded.pure, riskToBudget_bottom, RiskGrade.bottom, riskToBudget]

/-- τ respects `map` (functoriality of the component). -/
theorem tau_map {α β : Type} (f : α → β) (g : RGraded α) :
    tau (g.map f) = (tau g).map f := rfl

/-- **Lax `consume` coherence**: transporting a risk-`consume` through τ is
dominated by the corresponding budget-`consume`. The value is identical and the
resulting grade satisfies `τ(g.grade ⊔ r) ≤ τ(g.grade) ⊕ τ(r)`. This is the
graded monad-morphism square at the grade level. -/
theorem tau_consume_lax {α : Type} (g : RGraded α) (r : RiskGrade) :
    (tau (g.consume r)).value = (tau g).value ∧
    ((tau (g.consume r)).grade).le ((tau g).grade.saturatingAdd (riskToBudget r)) = true := by
  refine ⟨rfl, ?_⟩
  simp only [tau, RGraded.consume]
  exact riskToBudget_lax_monoidal g.grade r

/-! ## The remaining goal (stated, not yet proven — no `sorry`)

The full strong-naturality square over an arbitrary continuation `k : α → RGraded β`
— i.e. τ commutes with a graded `bind` up to the lax-monoidal inequality — is the
publishable extension. Stated here as a `Prop` so the goal is type-checked and
referenced by the spec/paper, without an unproven `theorem`. -/

/-- The open coherence: τ is a lax morphism of graded monads w.r.t. graded bind.
(`bind` composes grades by `join` on the risk side and by `⊕` on the budget side.) -/
abbrev TauStrongNaturalityGoal : Prop :=
  ∀ {α β : Type} (g : RGraded α) (k : α → RGraded β),
    ((tau (RGraded.mk (k g.value).value (g.grade.join (k g.value).grade))).grade).le
      ((tau g).grade.saturatingAdd (riskToBudget (k g.value).grade)) = true

end DLC
