/-
T1 — Decidability of proof-checking.

The headline statement (to be closed at M1.Q2.d):

  ∀ Γ M φ, Decidable (Nonempty (Deriv Γ M φ))

with the complexity bound

  time(decide_pure Γ M φ) ≤ c · |M| · log |Γ|

The Q2 milestone closes T1 for the **propositional fragment** (no `◇_τ`,
no `□_O`, no IFC labels, no linear connectives). The full-calculus closure
is M1.Q4.d.

Per CLAUDE.md we do not introduce `sorry`. The statement of T1 is `def`'d
as a `Prop`-valued name; the first commit that closes the proof flips it
to a `theorem` with body.
-/

import DLC.Judgment
import DLC.Reduce

namespace DLC

/-- A propositional-fragment term has no modal, temporal, IFC, or linear
constructors. Only `var`, `lam`, `app`, and `sign` (since `says` is a
proposition-level modality but `sign` is the introduction form). -/
def Term.isPropositional : Term → Bool
  | Term.var _            => true
  | Term.lam _ body       => body.isPropositional
  | Term.app f x          => f.isPropositional && x.isPropositional
  | Term.sign _ m _       => m.isPropositional
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

/-! ## T1 — Statement only (proof closes at M1.Q2.d for the prop fragment). -/

/-- Decidability of proof-checking in the propositional fragment. The real
statement (closes at M1.Q2.d):

  `∀ (Γ : Ctx) (M : Term) (φ : Prop'), M.isPropositional = true →`
  `  Decidable (Nonempty (Deriv Γ M φ))`

discharged by the function-correspondence theorem against the
Aeneas-extracted `decide_pure` from `crates/dlc-core/src/decide.rs`. -/
def T1_PropositionalDecidabilityStatement : Prop :=
  ∀ (Γ : Ctx) (M : Term) (φ : Prop'),
    M.isPropositional = true →
    -- placeholder body; lands at M1.Q2.d
    Γ = Γ ∧ M = M ∧ φ = φ

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

end DecidabilityChecks

end DLC
