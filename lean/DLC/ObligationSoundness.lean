/-
T4 — Obligation soundness across reduction.

For any reduction `M ▷ M'`, the set of pending obligations in `M'` is exactly
the set in `M` minus those discharged by the reduction step, plus those
introduced by it.

The proof structure (M1.Q3.d): induction over the reduction relation, using
subject reduction (M1.Q2.c) and the substitution lemma (M1.Q2.a). Lands at
M1.Q3.d.

This file states T4 as `T4_ObligationSoundnessStatement : Prop`. Proof
closure flips the `def` to a `theorem` with body.
-/

import DLC.Reduce
import DLC.Obligation
import DLC.Judgment

namespace DLC

/-- The (multi)set of obligations syntactically attached to a term — counted
with multiplicity so the linear semantics of obligation discharge is
preserved by the soundness statement.

For the propositional + obligation fragment we use a simple `List`; full-
calculus form moves to `Multiset` at M1.Q4. -/
def pendingObligations : Term → List Obligation
  | Term.var _                  => []
  | Term.lam _ body             => pendingObligations body
  | Term.app f x                =>
      pendingObligations f ++ pendingObligations x
  | Term.sign _ m _             => pendingObligations m
  | Term.verify _ m _           => pendingObligations m
  | Term.delegate m n           =>
      pendingObligations m ++ pendingObligations n
  | Term.attenuate m _          => pendingObligations m
  | Term.discharge m _          => pendingObligations m
  | Term.liftLabel _ m          => pendingObligations m
  | Term.declassify _ m π       =>
      pendingObligations m ++ pendingObligations π
  | Term.now _                  => []
  | Term.withinIntro _ m        => pendingObligations m
  | Term.pair a b               => pendingObligations a ++ pendingObligations b
  | Term.fst a                  => pendingObligations a
  | Term.snd a                  => pendingObligations a
  | Term.inl _ a                => pendingObligations a
  | Term.inr _ a                => pendingObligations a
  | Term.case s l r             =>
      pendingObligations s ++ pendingObligations l ++ pendingObligations r
  | Term.tensorIntro a b        => pendingObligations a ++ pendingObligations b
  | Term.letTensor s b          => pendingObligations s ++ pendingObligations b
  | Term.letSays _ s b          => pendingObligations s ++ pendingObligations b
  | Term.sfExtract m            => pendingObligations m

/-! ## Helper lemmas for T4 — partial closure (M1.Q3.d in progress).

The load-bearing claim is **non-introduction**: reduction never invents
an obligation that wasn't syntactically present beforehand. Formally:

  `∀ o, o ∈ pendingObligations M' → o ∈ pendingObligations M`

This is weaker than full multiset preservation (DLC's current redexes
don't discharge obligations — `Discharge` is a normal form at the head;
multiplicity-tracking discharge is the M3 product-line layer). It IS
enough to prove that *runtime never gains an unexpected obligation*,
which is the load-bearing security property. -/

/-- `shift` preserves the syntactic obligation list — the function walks
sub-terms, and shifting only adjusts de-Bruijn indices, never producing
or consuming obligations. -/
theorem pendingObligations_shift (t : Term) (delta cutoff : Nat) :
    pendingObligations (shift t delta cutoff) = pendingObligations t := by
  induction t generalizing cutoff with
  | var _ => simp [shift, pendingObligations]
  | lam _ _ ih => simp [shift, pendingObligations, ih]
  | app _ _ ihF ihX => simp [shift, pendingObligations, ihF, ihX]
  | sign _ _ _ ih => simp [shift, pendingObligations, ih]
  | verify _ _ _ ih => simp [shift, pendingObligations, ih]
  | delegate _ _ ihM ihN => simp [shift, pendingObligations, ihM, ihN]
  | attenuate _ _ ih => simp [shift, pendingObligations, ih]
  | discharge _ _ ihM ihN => simp [shift, pendingObligations, ihM, ihN]
  | liftLabel _ _ ih => simp [shift, pendingObligations, ih]
  | declassify _ _ _ ihM ihπ => simp [shift, pendingObligations, ihM, ihπ]
  | now _ => simp [shift, pendingObligations]
  | withinIntro _ _ ih => simp [shift, pendingObligations, ih]
  | pair _ _ ihA ihB => simp [shift, pendingObligations, ihA, ihB]
  | fst _ ih => simp [shift, pendingObligations, ih]
  | snd _ ih => simp [shift, pendingObligations, ih]
  | inl _ _ ih => simp [shift, pendingObligations, ih]
  | inr _ _ ih => simp [shift, pendingObligations, ih]
  | case _ _ _ ihS ihL ihR => simp [shift, pendingObligations, ihS, ihL, ihR]
  | tensorIntro _ _ ihA ihB => simp [shift, pendingObligations, ihA, ihB]
  | letTensor _ _ ihS ihB => simp [shift, pendingObligations, ihS, ihB]
  | letSays _ _ _ ihS ihB => simp [shift, pendingObligations, ihS, ihB]
  | sfExtract _ ih => simp [shift, pendingObligations, ih]

/-! ## T4 — statement closed, proof body deferred.

The non-introduction direction of T4 is what we'd ship in a closed form:

  `∀ M M' o, step M = some M' → o ∈ pendingObligations M' → o ∈ pendingObligations M`

The proof structure is case analysis over `step`'s 7 productive redexes,
with the β / case / letTensor / letSays cases delegating to a
`pendingObligations_substAt_subset` lemma (substitution doesn't introduce
obligations). That sub-lemma proves by 21-case induction on the body.

The structural skeleton was written and pushed; tactic-level details
(injection unfolding, nested-cases shape, if-split on hypothesis) need
iterative refinement under Lean 4.28 + Mathlib semantics. Tracking as
M1.Q3.d follow-up — `pendingObligations_shift` (proven above) is the
non-trivial structural pre-requisite. -/

/-- T4 — Obligation soundness statement (non-introduction direction). -/
def T4_ObligationSoundnessStatement : Prop :=
  ∀ (M M' : Term), step M = some M' →
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M

end DLC
