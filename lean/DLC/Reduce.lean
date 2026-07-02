/-
DLC — Small-step reduction.

Mirrors `crates/dlc-core/src/reduce.rs` case-for-case. The principal
reduction rules from `spec/typing-rules.md` §11: eight head redexes
plus the 2026-07 CONGRUENCE rules (ξ-rules) — when an elimination
form's head rule does not fire, reduction descends into the
scrutinee/function position, call-by-name, one deterministic position
per form. Without congruence, nested eliminations were stuck
(`π₁ (π₁ ⟨⟨a,b⟩,c⟩)` had no reduct) and progress failed; see
`spec/t3-two-run-design-2026-07.md` (FINDING, 2026-07-02).

`step` remains a FUNCTION, so reduction stays deterministic and the
`DLC.ReduceMeta` results (semi-confluence, Joinable transitivity)
apply unchanged.
-/

import DLC.Syntax
import DLC.Principal
import DLC.Subst
import DLC.Judgment

namespace DLC

/-- One deterministic step of reduction. `none` denotes a value, a
frozen form, or a term stuck on a frozen scrutinee. -/
def step : Term → Option Term
  -- β: (λ x:φ. body) arg ▷ body[arg/x]; ξ-app in the function position
  -- (call-by-name: the argument is never reduced).
  | Term.app f arg =>
      match f with
      | Term.lam _ body => some (subst body arg)
      | _ =>
          match step f with
          | some f' => some (Term.app f' arg)
          | none => none

  -- and-Eₗ-β: π₁ ⟨a, _⟩ ▷ a; ξ-fst.
  | Term.fst m =>
      match m with
      | Term.pair a _ => some a
      | _ =>
          match step m with
          | some m' => some (Term.fst m')
          | none => none

  -- and-Eᵣ-β: π₂ ⟨_, b⟩ ▷ b; ξ-snd.
  | Term.snd m =>
      match m with
      | Term.pair _ b => some b
      | _ =>
          match step m with
          | some m' => some (Term.snd m')
          | none => none

  -- or-E-β: case (inl _ a) of x ⇒ left | y ⇒ _ ▷ left[a/x] (inr
  -- symmetric); ξ-case on the scrutinee.
  | Term.case s left right =>
      match s with
      | Term.inl _ a => some (subst left a)
      | Term.inr _ a => some (subst right a)
      | _ =>
          match step s with
          | some s' => some (Term.case s' left right)
          | none => none

  -- tensor-E-β / let-tensor: `let x⊗y = a⊗b in body ▷ body[a/x, b/y]`;
  -- ξ-lettensor on the scrutinee.
  --
  -- The body has two bound variables, with `φ :: ψ :: Γ` convention
  -- (a:φ at index 0, b:ψ at index 1). Substitute a first (consumes
  -- index 0); `a` is typed in Γ, but the intermediate context after
  -- consuming `φ` is `ψ :: Γ`, so `a`'s free vars must shift up by 1
  -- to align with the ψ-binder now at index 0. After the second
  -- substitution (b at depth 0) the ψ-binder is consumed and we're
  -- back in Γ — b's free vars are already correct. This shift is
  -- required for typing preservation under the single-binder
  -- `propDeriv_subst` lemma; see `propDeriv_subject_reduction`.
  | Term.letTensor s body =>
      match s with
      | Term.tensorIntro a b => some (subst (subst body (shift a 1 0)) b)
      | _ =>
          match step s with
          | some s' => some (Term.letTensor s' body)
          | none => none

  -- says-extract / let-says: `let ⟨x⟩_p = ⟨m, _⟩_p in body ▷ body[m/x]`
  -- when the principals agree (a sign under the wrong principal is a
  -- stuck value — typing rules it out); ξ-letsays on the scrutinee.
  | Term.letSays p s body =>
      match s with
      | Term.sign p' m _ => if p = p' then some (subst body m) else none
      | _ =>
          match step s with
          | some s' => some (Term.letSays p s' body)
          | none => none

  -- sf-extract-β: `sfExtract (⟨m, _⟩_p)` exposes `m` (the speaks-for
  -- proposition's witness); ξ-sfextract on the scrutinee.
  | Term.sfExtract m =>
      match m with
      | Term.sign _ inner _ => some inner
      | _ =>
          match step m with
          | some m' => some (Term.sfExtract m')
          | none => none

  -- delegate-β: delegate(⟨_, _⟩_p, ⟨N, σ'⟩_q) ▷ ⟨N, σ'⟩_{p⊓q};
  -- ξ-delegate: left position first, then right once left is a sign.
  | Term.delegate m n =>
      match m, n with
      | Term.sign p _ _, Term.sign q inner sig' =>
          some (Term.sign (Principal.acting p q) inner sig')
      | Term.sign p mi si, _ =>
          match step n with
          | some n' => some (Term.delegate (Term.sign p mi si) n')
          | none => none
      | _, _ =>
          match step m with
          | some m' => some (Term.delegate m' n)
          | none => none

  -- Frozen forms and values: var, lam, sign, pair, inl, inr,
  -- tensorIntro, now, withinIntro, verify, attenuate, discharge,
  -- liftLabel, declassify. The frozen eliminations (verify, attenuate,
  -- declassify, discharge) are checked by the verifier layers rather
  -- than computed; discharge-β awaits the obligation-carrying
  -- constructor (T4 non-vacuity package).
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

/-! ## Subject reduction — real statement over the full `Deriv` judgment. -/

/-- Subject reduction (statement). If `Γ ⊢ M : φ` and `M ▷ M'`, then
`Γ ⊢ M' : φ`. The statement quantifies over the full `Deriv` judgment;
the proof for the propositional fragment lives in
`DLC.Decidability.propDeriv_subject_reduction`. Extending the proof to
the full `Deriv` is M1.Q2.c follow-up tracked separately. -/
def SubjectReductionStatement : Prop :=
  ∀ (Γ : Ctx) (M M' : Term) (φ : Prop'),
    step M = some M' →
    Nonempty (Deriv Γ M φ) →
    Nonempty (Deriv Γ M' φ)

end DLC
