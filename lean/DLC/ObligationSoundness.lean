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
  | var i =>
    -- `shift (Term.var i) delta cutoff` is a conditional; both branches
    -- evaluate to a `Term.var _` whose pendingObligations is `[]`.
    unfold shift
    split <;> rfl
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

/-- `substAt` doesn't introduce obligations: any obligation pending in
the result was either pending in the body or pending in the
substituted value. 21-case induction on the body.

This is the load-bearing sub-lemma for T4's `t4_no_new_obligation`
(the step-case analysis that goes on a follow-up PR). It is also the
key fact needed for the full multi-set obligation accounting of the
M3 runtime layer. -/
theorem pendingObligations_substAt_subset (body : Term) :
    ∀ (value : Term) (depth : Nat) (o : Obligation),
      o ∈ pendingObligations (substAt body value depth) →
      o ∈ pendingObligations body ∨ o ∈ pendingObligations value := by
  induction body with
  | var i =>
    intro value depth o hmem
    -- substAt (var i) value depth = if i = depth then shift value depth 0
    --                                else if i > depth then var (i-1)
    --                                else var i.
    -- In the i = depth case, the result has obligations(shift value ...)
    -- which equals obligations(value) by pendingObligations_shift.
    -- In the other two cases, the result is var _ with no obligations.
    unfold substAt at hmem
    split at hmem
    · right
      rw [pendingObligations_shift] at hmem
      exact hmem
    · split at hmem
      · simp [pendingObligations] at hmem
      · simp [pendingObligations] at hmem
  | lam _ inner ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value (depth + 1) o hmem
  | app _ _ ihF ihX =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hF | hX
    · rcases ihF value depth o hF with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihX value depth o hX with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | sign _ _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | verify _ _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | delegate _ _ ihM ihN =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hM | hN
    · rcases ihM value depth o hM with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihN value depth o hN with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | attenuate _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | discharge _ _ ihM ihN =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hM | hN
    · rcases ihM value depth o hM with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihN value depth o hN with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | liftLabel _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | declassify _ _ _ ihM ihπ =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hM | hπ
    · rcases ihM value depth o hM with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihπ value depth o hπ with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | now _ =>
    intro value depth o hmem
    unfold substAt at hmem
    simp [pendingObligations] at hmem
  | withinIntro _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | pair _ _ ihA ihB =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hA | hB
    · rcases ihA value depth o hA with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihB value depth o hB with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | fst _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | snd _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | inl _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | inr _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | case _ _ _ ihS ihL ihR =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hSL | hR
    · rcases List.mem_append.mp hSL with hS | hL
      · rcases ihS value depth o hS with h | h
        · left; simp [pendingObligations]; left; left; exact h
        · right; exact h
      · rcases ihL value (depth + 1) o hL with h | h
        · left; simp [pendingObligations]; left; right; exact h
        · right; exact h
    · rcases ihR value (depth + 1) o hR with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | tensorIntro _ _ ihA ihB =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hA | hB
    · rcases ihA value depth o hA with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihB value depth o hB with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | letTensor _ _ ihS ihB =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hS | hB
    · rcases ihS value depth o hS with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihB value (depth + 2) o hB with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | letSays _ _ _ ihS ihB =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    rcases List.mem_append.mp hmem with hS | hB
    · rcases ihS value depth o hS with h | h
      · left; simp [pendingObligations]; left; exact h
      · right; exact h
    · rcases ihB value (depth + 1) o hB with h | h
      · left; simp [pendingObligations]; right; exact h
      · right; exact h
  | sfExtract _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem

/-! ## T4 — statement; full closure on a follow-up PR.

`t4_no_new_obligation` (the step-case analysis using
`pendingObligations_substAt_subset`) goes on a follow-up PR to keep this
one focused on the substitution sub-lemma alone. The non-introduction
direction of T4 will then be `proven`. -/

/-- T4 — Obligation soundness statement (non-introduction direction). -/
def T4_ObligationSoundnessStatement : Prop :=
  ∀ (M M' : Term), step M = some M' →
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M

end DLC
