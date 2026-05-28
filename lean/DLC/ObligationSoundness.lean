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
  | app f x ihF ihX =>
    intro value depth o hmem
    -- definitionally: pendingObligations (substAt (Term.app f x) value depth)
    --   = pendingObligations (substAt f value depth) ++ pendingObligations (substAt x value depth)
    have hmem' : o ∈ pendingObligations (substAt f value depth) ++
                     pendingObligations (substAt x value depth) := hmem
    rcases List.mem_append.mp hmem' with hF | hX
    · rcases ihF value depth o hF with h | h
      · left
        show o ∈ pendingObligations f ++ pendingObligations x
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihX value depth o hX with h | h
      · left
        show o ∈ pendingObligations f ++ pendingObligations x
        exact List.mem_append.mpr (Or.inr h)
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
  | delegate m n ihM ihN =>
    intro value depth o hmem
    have hmem' : o ∈ pendingObligations (substAt m value depth) ++
                     pendingObligations (substAt n value depth) := hmem
    rcases List.mem_append.mp hmem' with hM | hN
    · rcases ihM value depth o hM with h | h
      · left
        show o ∈ pendingObligations m ++ pendingObligations n
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihN value depth o hN with h | h
      · left
        show o ∈ pendingObligations m ++ pendingObligations n
        exact List.mem_append.mpr (Or.inr h)
      · right; exact h
  | attenuate _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | discharge _ _ ihM _ =>
    -- pendingObligations of `discharge m n` is `pendingObligations m` only
    -- (n is the obligation-evidence term and is consumed by discharge;
    -- counting its obligations would double-count). Single-subterm shape.
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ihM value depth o hmem
  | liftLabel _ _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem
  | declassify _ m π ihM ihπ =>
    intro value depth o hmem
    have hmem' : o ∈ pendingObligations (substAt m value depth) ++
                     pendingObligations (substAt π value depth) := hmem
    rcases List.mem_append.mp hmem' with hM | hπ
    · rcases ihM value depth o hM with h | h
      · left
        show o ∈ pendingObligations m ++ pendingObligations π
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihπ value depth o hπ with h | h
      · left
        show o ∈ pendingObligations m ++ pendingObligations π
        exact List.mem_append.mpr (Or.inr h)
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
  | pair a b ihA ihB =>
    intro value depth o hmem
    have hmem' : o ∈ pendingObligations (substAt a value depth) ++
                     pendingObligations (substAt b value depth) := hmem
    rcases List.mem_append.mp hmem' with hA | hB
    · rcases ihA value depth o hA with h | h
      · left
        show o ∈ pendingObligations a ++ pendingObligations b
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihB value depth o hB with h | h
      · left
        show o ∈ pendingObligations a ++ pendingObligations b
        exact List.mem_append.mpr (Or.inr h)
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
  | case s l r ihS ihL ihR =>
    intro value depth o hmem
    -- pendingObligations of case is (S ++ L) ++ R (left-associated).
    have hmem' : o ∈ (pendingObligations (substAt s value depth) ++
                       pendingObligations (substAt l value (depth + 1))) ++
                     pendingObligations (substAt r value (depth + 1)) := hmem
    rcases List.mem_append.mp hmem' with hSL | hR
    · rcases List.mem_append.mp hSL with hS | hL
      · rcases ihS value depth o hS with h | h
        · left
          show o ∈ (pendingObligations s ++ pendingObligations l) ++ pendingObligations r
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))
        · right; exact h
      · rcases ihL value (depth + 1) o hL with h | h
        · left
          show o ∈ (pendingObligations s ++ pendingObligations l) ++ pendingObligations r
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
        · right; exact h
    · rcases ihR value (depth + 1) o hR with h | h
      · left
        show o ∈ (pendingObligations s ++ pendingObligations l) ++ pendingObligations r
        exact List.mem_append.mpr (Or.inr h)
      · right; exact h
  | tensorIntro a b ihA ihB =>
    intro value depth o hmem
    have hmem' : o ∈ pendingObligations (substAt a value depth) ++
                     pendingObligations (substAt b value depth) := hmem
    rcases List.mem_append.mp hmem' with hA | hB
    · rcases ihA value depth o hA with h | h
      · left
        show o ∈ pendingObligations a ++ pendingObligations b
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihB value depth o hB with h | h
      · left
        show o ∈ pendingObligations a ++ pendingObligations b
        exact List.mem_append.mpr (Or.inr h)
      · right; exact h
  | letTensor s b ihS ihB =>
    intro value depth o hmem
    have hmem' : o ∈ pendingObligations (substAt s value depth) ++
                     pendingObligations (substAt b value (depth + 2)) := hmem
    rcases List.mem_append.mp hmem' with hS | hB
    · rcases ihS value depth o hS with h | h
      · left
        show o ∈ pendingObligations s ++ pendingObligations b
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihB value (depth + 2) o hB with h | h
      · left
        show o ∈ pendingObligations s ++ pendingObligations b
        exact List.mem_append.mpr (Or.inr h)
      · right; exact h
  | letSays _ s b ihS ihB =>
    intro value depth o hmem
    have hmem' : o ∈ pendingObligations (substAt s value depth) ++
                     pendingObligations (substAt b value (depth + 1)) := hmem
    rcases List.mem_append.mp hmem' with hS | hB
    · rcases ihS value depth o hS with h | h
      · left
        show o ∈ pendingObligations s ++ pendingObligations b
        exact List.mem_append.mpr (Or.inl h)
      · right; exact h
    · rcases ihB value (depth + 1) o hB with h | h
      · left
        show o ∈ pendingObligations s ++ pendingObligations b
        exact List.mem_append.mpr (Or.inr h)
      · right; exact h
  | sfExtract _ ih =>
    intro value depth o hmem
    unfold substAt at hmem
    unfold pendingObligations at hmem
    exact ih value depth o hmem

/-! ## T4 — Proven (non-introduction direction).

The case analysis over `step`'s 7 productive redexes uses
`pendingObligations_substAt_subset` for the four substitution-style
redexes (β, case, letTensor, letSays) and direct list-membership
arithmetic for the three rearrangement redexes (delegate, fst/snd,
sfExtract). The remaining 14 outer constructors contradict the
`step M = some M'` hypothesis. -/

/-- T4 — Reduction never introduces a new obligation. -/
theorem t4_no_new_obligation
    (M M' : Term) (h : step M = some M') :
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M := by
  intro o hmem
  cases M with
  | var _ => simp [step] at h
  | lam _ _ => simp [step] at h
  | app f x =>
    -- β is the only productive sub-case; all other f shapes give none.
    cases f with
    | lam _ body =>
      -- step (app (lam _ body) x) = some (subst body x)
      -- so by injection, M' = subst body x.
      simp only [step] at h
      -- h : some (subst body x) = some M'
      -- Inject: M' = subst body x. We rewrite hmem using the equality.
      have hM' : M' = subst body x := by
        have := Option.some.inj h
        exact this.symm
      rw [hM'] at hmem
      -- hmem : o ∈ pendingObligations (subst body x)
      -- subst body x = substAt body x 0 by defn of subst.
      have hsub : o ∈ pendingObligations (substAt body x 0) := hmem
      rcases pendingObligations_substAt_subset body x 0 o hsub with hB | hX
      · show o ∈ pendingObligations body ++ pendingObligations x
        exact List.mem_append.mpr (Or.inl hB)
      · show o ∈ pendingObligations body ++ pendingObligations x
        exact List.mem_append.mpr (Or.inr hX)
    | _ => simp [step] at h
  | sign _ _ _ => simp [step] at h
  | verify _ _ _ => simp [step] at h
  | delegate m n =>
    -- delegate-β: only fires when both m and n are signs.
    cases m with
    | sign p _ _ =>
      cases n with
      | sign q inner sig' =>
        -- step (delegate (sign p _ _) (sign q inner sig'))
        --   = some (sign (acting p q) inner sig')
        simp only [step] at h
        have hM' : M' = Term.sign (Principal.acting p q) inner sig' :=
          (Option.some.inj h).symm
        rw [hM'] at hmem
        -- hmem : o ∈ pendingObligations (Term.sign _ inner _)
        --      = pendingObligations inner
        show o ∈ pendingObligations (Term.sign p _ _) ++
                  pendingObligations (Term.sign q inner sig')
        exact List.mem_append.mpr (Or.inr hmem)
      | _ => simp [step] at h
    | _ => simp [step] at h
  | attenuate _ _ => simp [step] at h
  | discharge _ _ => simp [step] at h
  | liftLabel _ _ => simp [step] at h
  | declassify _ _ _ => simp [step] at h
  | now _ => simp [step] at h
  | withinIntro _ _ => simp [step] at h
  | pair _ _ => simp [step] at h
  | fst t =>
    cases t with
    | pair a b =>
      -- step (fst (pair a b)) = some a, so M' = a.
      simp only [step] at h
      have hM' : M' = a := (Option.some.inj h).symm
      rw [hM'] at hmem
      -- hmem : o ∈ pendingObligations a
      show o ∈ pendingObligations a ++ pendingObligations b
      exact List.mem_append.mpr (Or.inl hmem)
    | _ => simp [step] at h
  | snd t =>
    cases t with
    | pair a b =>
      simp only [step] at h
      have hM' : M' = b := (Option.some.inj h).symm
      rw [hM'] at hmem
      show o ∈ pendingObligations a ++ pendingObligations b
      exact List.mem_append.mpr (Or.inr hmem)
    | _ => simp [step] at h
  | inl _ _ => simp [step] at h
  | inr _ _ => simp [step] at h
  | case scrut left right =>
    -- Two productive sub-cases: scrut = inl _ a or inr _ a.
    cases scrut with
    | inl _ a =>
      -- step (case (inl _ a) left right) = some (subst left a)
      simp only [step] at h
      have hM' : M' = subst left a := (Option.some.inj h).symm
      rw [hM'] at hmem
      have hsub : o ∈ pendingObligations (substAt left a 0) := hmem
      rcases pendingObligations_substAt_subset left a 0 o hsub with hL | hA
      · -- o was in left's obligations -- goes into the (S ++ L) ++ R slot via (left of outer)
        show o ∈ (pendingObligations (Term.inl _ a) ++ pendingObligations left) ++ pendingObligations right
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hL)))
      · -- o was in a's obligations; a is inside (inl _ a) so it goes via the scrutinee
        show o ∈ (pendingObligations (Term.inl _ a) ++ pendingObligations left) ++ pendingObligations right
        -- pendingObligations (Term.inl _ a) = pendingObligations a
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hA)))
    | inr _ a =>
      simp only [step] at h
      have hM' : M' = subst right a := (Option.some.inj h).symm
      rw [hM'] at hmem
      have hsub : o ∈ pendingObligations (substAt right a 0) := hmem
      rcases pendingObligations_substAt_subset right a 0 o hsub with hR | hA
      · show o ∈ (pendingObligations (Term.inr _ a) ++ pendingObligations left) ++ pendingObligations right
        exact List.mem_append.mpr (Or.inr hR)
      · show o ∈ (pendingObligations (Term.inr _ a) ++ pendingObligations left) ++ pendingObligations right
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hA)))
    | _ => simp [step] at h
  | tensorIntro _ _ => simp [step] at h
  | letTensor scrut body =>
    cases scrut with
    | tensorIntro a b =>
      -- step (letTensor (tensorIntro a b) body) = some (subst (subst body (shift a 1 0)) b).
      -- The `shift a 1 0` is a no-op on pendingObligations (it only
      -- renumbers free variables), so the obligation-membership reasoning
      -- is identical to the un-shifted version.
      simp only [step] at h
      have hM' : M' = subst (subst body (shift a 1 0)) b := (Option.some.inj h).symm
      rw [hM'] at hmem
      have hsub : o ∈ pendingObligations
                       (substAt (substAt body (shift a 1 0) 0) b 0) := hmem
      rcases pendingObligations_substAt_subset
              (substAt body (shift a 1 0) 0) b 0 o hsub with hBodyA | hB
      · -- o was in the substituted-body; recurse, with the shift collapsed.
        rcases pendingObligations_substAt_subset body (shift a 1 0) 0 o hBodyA
          with hBody | hA
        · -- o in body
          show o ∈ pendingObligations (Term.tensorIntro a b) ++ pendingObligations body
          exact List.mem_append.mpr (Or.inr hBody)
        · -- o in shift a 1 0 = pendingObligations a (by pendingObligations_shift)
          show o ∈ pendingObligations (Term.tensorIntro a b) ++ pendingObligations body
          rw [pendingObligations_shift] at hA
          exact List.mem_append.mpr (Or.inl
            (show o ∈ pendingObligations a ++ pendingObligations b from
              List.mem_append.mpr (Or.inl hA)))
      · -- o in b (inside tensorIntro)
        show o ∈ pendingObligations (Term.tensorIntro a b) ++ pendingObligations body
        exact List.mem_append.mpr (Or.inl
          (show o ∈ pendingObligations a ++ pendingObligations b from
            List.mem_append.mpr (Or.inr hB)))
    | _ => simp [step] at h
  | letSays p scrut body =>
    cases scrut with
    | sign p' m _ =>
      -- step (letSays p (sign p' m _) body) = if p = p' then some (subst body m) else none
      simp only [step] at h
      split at h
      · -- p = p' case
        have hM' : M' = subst body m := (Option.some.inj h).symm
        rw [hM'] at hmem
        have hsub : o ∈ pendingObligations (substAt body m 0) := hmem
        rcases pendingObligations_substAt_subset body m 0 o hsub with hBody | hM
        · show o ∈ pendingObligations (Term.sign p' m _) ++ pendingObligations body
          exact List.mem_append.mpr (Or.inr hBody)
        · -- o was in m (inside sign p' m _), so in pendingObligations of scrut
          show o ∈ pendingObligations (Term.sign p' m _) ++ pendingObligations body
          exact List.mem_append.mpr (Or.inl hM)
      · -- p ≠ p' case: step returned none, contradicts hypothesis.
        simp at h
    | _ => simp [step] at h
  | sfExtract t =>
    cases t with
    | sign _ m _ =>
      -- step (sfExtract (sign _ m _)) = some m
      simp only [step] at h
      have hM' : M' = m := (Option.some.inj h).symm
      rw [hM'] at hmem
      -- hmem : o ∈ pendingObligations m
      -- goal : o ∈ pendingObligations (Term.sfExtract (Term.sign _ m _))
      --       = pendingObligations (Term.sign _ m _) = pendingObligations m
      exact hmem
    | _ => simp [step] at h

/-- T4 — Obligation soundness statement (non-introduction direction).
Kept as `abbrev` aliasing the proved theorem's statement. -/
abbrev T4_ObligationSoundnessStatement : Prop :=
  ∀ (M M' : Term), step M = some M' →
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M

end DLC
