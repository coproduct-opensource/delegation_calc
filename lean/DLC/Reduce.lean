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

  -- and-Eₗ-β: π₁ ⟨a, _⟩ ▷ a
  | Term.fst (Term.pair a _) => some a

  -- and-Eᵣ-β: π₂ ⟨_, b⟩ ▷ b
  | Term.snd (Term.pair _ b) => some b

  -- or-E-β-left: case (inl _ a) of x ⇒ left | y ⇒ _ ▷ left[a/x]
  | Term.case (Term.inl _ a) left _ => some (subst left a)

  -- or-E-β-right: symmetric.
  | Term.case (Term.inr _ a) _ right => some (subst right a)

  -- tensor-E-β / let-tensor: `let x⊗y = a⊗b in body ▷ body[a/x, b/y]`.
  -- The body has two bound variables; we substitute twice (outer first).
  | Term.letTensor (Term.tensorIntro a b) body =>
      some (subst (subst body a) b)

  -- says-extract / let-says: `let ⟨x⟩_p = ⟨m, _⟩_p in body ▷ body[m/x]`.
  | Term.letSays p (Term.sign p' m _) body =>
      if p = p' then some (subst body m) else none

  -- sf-extract reduction: `sfExtract (⟨m, _⟩_p)` exposes `m` (the
  -- speaks-for proposition's witness).
  | Term.sfExtract (Term.sign _ m _) => some m

  -- Other constructors at head are normal forms. attenuate, discharge,
  -- withinIntro normalize through `verify` rather than the head reducer.
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
      = some (Term.var 5) := rfl

/-- Var is a normal form. -/
example : step (Term.var 0) = none := rfl

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
