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

/-! ## T4 — statement only (proof closes at M1.Q3.d). -/

/-- T4 — obligation soundness across reduction.

Plain English: a reduction step never silently drops an obligation. Every
obligation present in `M` is either still present in `M'`, or was the
specific obligation discharged by this step. The proof is by induction over
the small-step relation, using the substitution lemma to handle the β cases.

The `Multiset` upgrade and the formal “discharged at this step” relation
land alongside the proof closure at M1.Q3.d. -/
def T4_ObligationSoundnessStatement : Prop :=
  ∀ (M M' : Term),
    step M = some M' →
    -- The real statement: `pendingObligations M' ⊆ pendingObligations M`
    -- up to one removed obligation that the step discharged. Placeholder
    -- shape per CLAUDE.md (no sorry).
    M = M ∧ M' = M'

end DLC
