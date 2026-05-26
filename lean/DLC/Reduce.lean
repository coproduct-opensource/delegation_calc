/-
DLC — Small-step reduction.

Mirrors `crates/dlc-core/src/reduce.rs`. The principal reduction rules from
`spec/typing-rules.md` §11; head-position only. Subject reduction is the
load-bearing theorem to close at M1.Q2.c (proof closure depends on the
substitution lemma from M1.Q2.a).
-/

import DLC.Syntax
import DLC.Principal
import DLC.Subst

namespace DLC

/-- One step of head reduction. `none` denotes a normal form. -/
def step : Term → Option Term
  -- β: (λ x:φ. body) arg ▷ body[arg/x]
  | Term.app (Term.lam _ body) arg =>
      some (subst body arg)

  -- delegate-β: delegate(⟨_, _⟩_p, ⟨N, σ'⟩_q) ▷ ⟨N, σ'⟩_{p⊓q}
  | Term.delegate (Term.sign p _ _) (Term.sign q inner sig') =>
      some (Term.sign (Principal.acting p q) inner sig')

  -- Other constructors at head are normal forms. attenuate, discharge,
  -- withinIntro are normal forms in this kernel; their elimination logic
  -- lives in the verifier (the calculus's `verify` rule), not here.
  | _ => none

/-- Iterate `step` up to `fuel` steps, returning the final term and the step
count actually taken. Total by construction. -/
def reduceWithFuel : Term → Nat → Term × Nat
  | t, 0 => (t, 0)
  | t, n+1 =>
      match step t with
      | none => (t, 0)
      | some t' =>
          let (final, k) := reduceWithFuel t' n
          (final, k + 1)

/-! ## Sanity checks for the step function. -/

namespace ReduceChecks

/-- β: identity applied to `Var 5` reduces to `Var 5`. -/
example :
    step (Term.app (Term.lam (Prop'.atom 0) (Term.var 0)) (Term.var 5))
      = some (Term.var 5) := by
  decide

/-- Var is a normal form. -/
example : step (Term.var 0) = none := by decide

end ReduceChecks

/-! ## Subject reduction — statement only (proof at M1.Q2.c). -/

/-- Subject reduction (statement). If `Γ ⊢ M : φ` and `M ▷ M'`, then
`Γ ⊢ M' : φ`. Closure requires the substitution lemma; both land at M1.Q2. -/
def SubjectReductionStatement : Prop :=
  ∀ (M M' : Term), step M = some M' →
    -- Real statement (once Deriv is fully populated): ∀ Γ φ,
    --   Deriv Γ M φ → Deriv Γ M' φ.
    -- Placeholder: parametric in the inputs so the type is `Prop`.
    M = M ∧ M' = M'

end DLC
