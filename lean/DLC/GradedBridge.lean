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

## What calculus is this?

A **graded (modal) effect–coeffect calculus** — graded modal type theory, layered
over DLC's substructural (linear) modal authorization logic. The two grades are
**(partially) ordered monoids**:

  * `RiskGrade` is a graded *monad* grade — an *effect* (a bounded join-semilattice,
    i.e. an idempotent commutative ordered monoid `(⊔, ⊥)`); risk only accumulates.
  * `DpBudget` is a graded *comonad* grade — a *coeffect* (the additive monoid
    `(ℕ², +, 0)`); the differential-privacy *sensitivity* coeffect.

`τ` is a **monotone lax monoid homomorphism** from the `(⊔,⊥)` monoid to the `(⊕,0)`
monoid, lifted to a natural transformation of the graded functors. "Lax" because it
preserves the tensor only up to the order: `τ(a ⊔ b) ≤ τ(a) ⊕ τ(b)` (the unit is
preserved on the nose, `τ ⊥ = 0`). Categorically, a lax monoidal functor between
posetal monoidal categories. This is NOT a π-calculus / process algebra: there are no
channels, name-passing, or mobile processes — only graded modalities over a typed core.

References:
  * Katsumata — *Parametric effect monads and semantics of effect systems* (POPL 2014):
    graded monads / effect systems (the `RiskGrade` side).
  * Petricek, Mycroft, Orchard — *Coeffects: Unified Static Analysis of
    Context-Dependence* (ICALP 2013) / graded comonads (the `DpBudget` side).
  * Gaboardi, Katsumata, Orchard, Breuvart, Uustalu — *Combining Effects and Coeffects
    via Grading* (ICFP 2016): the closest prior art — bridging a graded monad and a
    graded comonad. `τ` lives in this program; the open `TauStrongNaturalityGoal`
    below is the distributive-law/strong-naturality step.
  * Reed & Pierce — *Distance Makes the Types Grow Stronger* (ICFP 2010, *Fuzz*):
    differential privacy as a sensitivity coeffect — the `DpBudget` lineage.
  * Orchard, Liepelt, Eades — *Quantitative Program Reasoning with Graded Modal Types*
    (ICFP 2019, *Granule*): the language realization of graded modal types.
  * Atkey — *Parameterised notions of computation* (the indexed/graded `T^ℓ` shape).

Novelty (not in Mathlib, not in the literature for this pairing): bridging two
*different* gradings — a join-semilattice effect grade and an additive coeffect grade —
with the lax coherence, for the risk ↔ differential-privacy correspondence specifically.
-/

import DLC.Graded
import Mathlib.Tactic.DeriveFintype

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

theorem join_comm (a b : RiskGrade) : join a b = join b a := by
  cases a <;> cases b <;> decide
theorem join_assoc (a b c : RiskGrade) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> decide
theorem join_idem (a : RiskGrade) : join a a = a := by cases a <;> decide
theorem join_bottom_left (a : RiskGrade) : join bottom a = a := by cases a <;> decide

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
    a.rank ≤ b.rank → (riskToBudget a).le (riskToBudget b) = true := by
  cases a <;> cases b <;> decide

/-- **The lax-monoidal coherence** — the heart of the bridge:
`τ(a ⊔ b) ≤ τ(a) ⊕ τ(b)`. Join-grade composition is dominated by additive-grade
composition, so collapsing a risk join into a budget sum is always sound (never
under-charges). Kernel-checked by `decide` over the finite grade pairs. -/
theorem riskToBudget_lax_monoidal (a b : RiskGrade) :
    (riskToBudget (RiskGrade.join a b)).le
      ((riskToBudget a).saturatingAdd (riskToBudget b)) = true := by
  cases a <;> cases b <;> decide

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

/-- Graded `bind`: run `k` on the value, composing grades by JOIN (the effect grade of
the whole is the join of the parts — risk only rises). -/
def bind {α β : Type} (g : RGraded α) (k : α → RGraded β) : RGraded β :=
  ⟨(k g.value).value, g.grade.join (k g.value).grade⟩

end RGraded

/-- The natural transformation τ on carriers: keep the value, map the grade. -/
def tau {α : Type} (g : RGraded α) : Graded α :=
  ⟨g.value, riskToBudget g.grade⟩

/-- τ preserves the underlying value (the natural-transformation component is
identity on values). -/
@[simp] theorem tau_value {α : Type} (g : RGraded α) : (tau g).value = g.value := rfl

/-- τ respects `pure`: `τ (pure a) = pure a`. (Unit preservation — half of the
monad-morphism laws.) -/
theorem tau_pure {α : Type} (a : α) : tau (RGraded.pure a) = Graded.pure a := rfl

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

/-! ## Strong naturality over graded `bind` (M1 — now proven)

τ is a lax morphism of graded monads: it commutes with graded `bind` up to the
lax-monoidal inequality. `bind` composes grades by `⊔` on the risk side; τ sends that
to `⊕` on the budget side, dominated by the sum. This is the square that was previously
only stated. -/

/-- The morphism-of-graded-monads law over `bind`: τ preserves the value, and the budget
τ assigns the bound computation is `≤` the sum of the budgets of the parts. -/
theorem tau_bind_lax {α β : Type} (g : RGraded α) (k : α → RGraded β) :
    (tau (g.bind k)).value = (k g.value).value ∧
    ((tau (g.bind k)).grade).le
      ((tau g).grade.saturatingAdd (riskToBudget (k g.value).grade)) = true := by
  refine ⟨rfl, ?_⟩
  simp only [tau, RGraded.bind]
  exact riskToBudget_lax_monoidal g.grade (k g.value).grade

/-- The strong-naturality coherence (grade level) — now discharged, not merely stated. -/
abbrev TauStrongNaturalityGoal : Prop :=
  ∀ {α β : Type} (g : RGraded α) (k : α → RGraded β),
    ((tau (g.bind k)).grade).le
      ((tau g).grade.saturatingAdd (riskToBudget (k g.value).grade)) = true

theorem tau_strong_naturality : TauStrongNaturalityGoal :=
  fun g k => (tau_bind_lax g k).2

/-! ## A consumer: risk-adaptive DP admission control

Per the adoption discipline (a morphism nobody consumes is shelfware), a theorem that
USES the bridge to gate a real decision. `admitsUnderCap` admits a risk-graded
computation iff the DP budget τ assigns its risk grade fits a cap; `admits_compose`
shows the bound *composes*: you may check the parts against the cap rather than
re-deriving the composite, because the lax square bounds the whole by the sum. -/

/-- Componentwise transitivity of the DP-budget order (the glue the consumer needs). -/
theorem DpBudget.le_trans {a b c : DpBudget}
    (hab : a.le b = true) (hbc : b.le c = true) : a.le c = true := by
  simp only [DpBudget.le, decide_eq_true_eq] at *
  exact ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩

/-- Admission control: admit `g` iff the DP budget τ assigns its risk grade fits `cap`.
This is the risk-adaptive DP policy — a higher risk grade maps to a larger (tighter to
admit) budget. -/
def admitsUnderCap {α : Type} (g : RGraded α) (cap : DpBudget) : Bool :=
  (tau g).grade.le cap

/-- **The consumer pays off the proof.** If the *summed* budget of the two steps fits
the cap, the *bound* computation is admitted — checking the parts suffices, by the lax
square. Without `tau_strong_naturality` you would have to re-derive the composite grade;
with it, admissibility is compositional. -/
theorem admits_compose {α β : Type} (g : RGraded α) (k : α → RGraded β) (cap : DpBudget)
    (h : ((tau g).grade.saturatingAdd (riskToBudget (k g.value).grade)).le cap = true) :
    admitsUnderCap (g.bind k) cap = true := by
  unfold admitsUnderCap
  exact DpBudget.le_trans (tau_strong_naturality g k) h

end DLC
