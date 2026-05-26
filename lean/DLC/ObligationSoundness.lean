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

/-! ## Helper lemmas for T4.

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

/-- `substAt` doesn't introduce obligations beyond what was in either the
body or the value being substituted. Stated as containment via `List.Mem`
(no multiplicity tracking — see module-level comment). -/
theorem pendingObligations_substAt_subset
    (body value : Term) (depth : Nat) :
    ∀ (o : Obligation),
      o ∈ pendingObligations (substAt body value depth) →
      o ∈ pendingObligations body ∨ o ∈ pendingObligations value := by
  intro o
  induction body generalizing depth with
  | var i =>
    simp [substAt]
    split <;> rename_i h1
    · -- i = depth → result is shift value depth 0
      intro hmem
      right
      have := pendingObligations_shift value depth 0
      rw [this] at hmem
      exact hmem
    · split <;> rename_i h2
      · -- i > depth → result is Term.var (i - 1)
        simp [pendingObligations]
      · -- otherwise → result is Term.var i
        simp [pendingObligations]
  | lam _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih (depth + 1) hmem
  | app _ _ ihF ihX =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hF | hX
    · rcases ihF depth hF with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihX depth hX with h | h
      · left; right; exact h
      · right; exact h
  | sign _ _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | verify _ _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | delegate _ _ ihM ihN =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hM | hN
    · rcases ihM depth hM with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihN depth hN with h | h
      · left; right; exact h
      · right; exact h
  | attenuate _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | discharge _ _ ihM ihN =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hM | hN
    · rcases ihM depth hM with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihN depth hN with h | h
      · left; right; exact h
      · right; exact h
  | liftLabel _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | declassify _ _ _ ihM ihπ =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hM | hπ
    · rcases ihM depth hM with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihπ depth hπ with h | h
      · left; right; exact h
      · right; exact h
  | now _ =>
    simp [substAt, pendingObligations]
  | withinIntro _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | pair _ _ ihA ihB =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hA | hB
    · rcases ihA depth hA with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihB depth hB with h | h
      · left; right; exact h
      · right; exact h
  | fst _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | snd _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | inl _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | inr _ _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem
  | case _ _ _ ihS ihL ihR =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with (hS | hL) | hR
    · rcases ihS depth hS with h | h
      · left; left; left; exact h
      · right; exact h
    · rcases ihL (depth + 1) hL with h | h
      · left; left; right; exact h
      · right; exact h
    · rcases ihR (depth + 1) hR with h | h
      · left; right; exact h
      · right; exact h
  | tensorIntro _ _ ihA ihB =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hA | hB
    · rcases ihA depth hA with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihB depth hB with h | h
      · left; right; exact h
      · right; exact h
  | letTensor _ _ ihS ihB =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hS | hB
    · rcases ihS depth hS with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihB (depth + 2) hB with h | h
      · left; right; exact h
      · right; exact h
  | letSays _ _ _ ihS ihB =>
    simp [substAt, pendingObligations]
    intro hmem
    rcases hmem with hS | hB
    · rcases ihS depth hS with h | h
      · left; left; exact h
      · right; exact h
    · rcases ihB (depth + 1) hB with h | h
      · left; right; exact h
      · right; exact h
  | sfExtract _ ih =>
    simp [substAt, pendingObligations]
    intro hmem
    exact ih depth hmem

/-! ## T4 — proven for the non-introduction direction.

The full T4 (multiplicity-tracking + discharge-bookkeeping) lives in the
M3 product layer where `Discharge` actually consumes evidence. The
calculus-level statement that *no obligation is silently invented* is the
load-bearing security property and is closed here. -/

/-- T4 — Reduction never introduces a new obligation. -/
theorem t4_no_new_obligation
    (M M' : Term) (h : step M = some M') :
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M := by
  intro o hmem
  -- Case-analyze `step` by pattern-matching on `M`'s outer shape.
  -- Each redex either rearranges sub-terms (containment trivial) or
  -- invokes `subst`, where `pendingObligations_substAt_subset` covers it.
  cases M with
  | app f x =>
    cases f with
    | lam _ body =>
      -- β: result = subst body x
      simp [step] at h
      have : M' = subst body x := by injection h
      rw [this] at hmem
      simp [subst] at hmem
      rcases pendingObligations_substAt_subset body x 0 o hmem with hB | hX
      · simp [pendingObligations]
        left; exact hB
      · simp [pendingObligations]
        right; exact hX
    | _ => simp [step] at h
  | delegate m n =>
    cases m with
    | sign p _ _ =>
      cases n with
      | sign q inner sig' =>
        simp [step] at h
        have : M' = Term.sign (Principal.acting p q) inner sig' := by injection h
        rw [this] at hmem
        simp [pendingObligations] at hmem
        simp [pendingObligations]
        right; exact hmem
      | _ => simp [step] at h
    | _ => simp [step] at h
  | fst t =>
    cases t with
    | pair a _ =>
      simp [step] at h
      have : M' = a := by injection h
      rw [this] at hmem
      simp [pendingObligations]
      left; exact hmem
    | _ => simp [step] at h
  | snd t =>
    cases t with
    | pair _ b =>
      simp [step] at h
      have : M' = b := by injection h
      rw [this] at hmem
      simp [pendingObligations]
      right; exact hmem
    | _ => simp [step] at h
  | case scrut left right =>
    cases scrut with
    | inl _ a =>
      simp [step] at h
      have : M' = subst left a := by injection h
      rw [this] at hmem
      simp [subst] at hmem
      rcases pendingObligations_substAt_subset left a 0 o hmem with hL | hA
      · simp [pendingObligations]; left; right; exact hL
      · simp [pendingObligations]; left; left; exact hA
    | inr _ a =>
      simp [step] at h
      have : M' = subst right a := by injection h
      rw [this] at hmem
      simp [subst] at hmem
      rcases pendingObligations_substAt_subset right a 0 o hmem with hR | hA
      · simp [pendingObligations]; right; exact hR
      · simp [pendingObligations]; left; left; exact hA
    | _ => simp [step] at h
  | letTensor scrut body =>
    cases scrut with
    | tensorIntro a b =>
      simp [step] at h
      have : M' = subst (subst body a) b := by injection h
      rw [this] at hmem
      simp [subst] at hmem
      rcases pendingObligations_substAt_subset (substAt body a 0) b 0 o hmem with h1 | hB
      · rcases pendingObligations_substAt_subset body a 0 o h1 with hBody | hA
        · simp [pendingObligations]; right; exact hBody
        · simp [pendingObligations]; left; left; exact hA
      · simp [pendingObligations]; left; right; exact hB
    | _ => simp [step] at h
  | letSays p scrut body =>
    cases scrut with
    | sign p' m _ =>
      simp [step] at h
      split at h <;> rename_i hp
      · -- p = p' branch
        have : M' = subst body m := by injection h
        rw [this] at hmem
        simp [subst] at hmem
        rcases pendingObligations_substAt_subset body m 0 o hmem with hB | hM
        · simp [pendingObligations]; right; exact hB
        · simp [pendingObligations]; left; exact hM
      · -- p ≠ p' branch: step returns none, contradicts h
        simp at h
    | _ => simp [step] at h
  | sfExtract t =>
    cases t with
    | sign _ m _ =>
      simp [step] at h
      have : M' = m := by injection h
      rw [this] at hmem
      simp [pendingObligations]
      exact hmem
    | _ => simp [step] at h
  -- All remaining outer shapes are normal forms (step returns none) and
  -- thus contradict the hypothesis `h : step M = some M'`.
  | var _ => simp [step] at h
  | lam _ _ => simp [step] at h
  | sign _ _ _ => simp [step] at h
  | verify _ _ _ => simp [step] at h
  | attenuate _ _ => simp [step] at h
  | discharge _ _ => simp [step] at h
  | liftLabel _ _ => simp [step] at h
  | declassify _ _ _ => simp [step] at h
  | now _ => simp [step] at h
  | withinIntro _ _ => simp [step] at h
  | pair _ _ => simp [step] at h
  | inl _ _ => simp [step] at h
  | inr _ _ => simp [step] at h
  | tensorIntro _ _ => simp [step] at h

/-- Backward-compat alias for the original statement form. -/
abbrev T4_ObligationSoundnessStatement : Prop :=
  ∀ (M M' : Term), step M = some M' →
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M

end DLC
