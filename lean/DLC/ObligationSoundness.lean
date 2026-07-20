/-
T4 — Obligation soundness across reduction.

## Status: NO LONGER VACUOUS as of R5 (2026-07-20).

`t4_no_new_obligation` is a ~180-line case analysis over `step`'s redexes.
Until R5 it quantified over members of a list that was provably ALWAYS
EMPTY: no `Term` constructor carried an `Obligation`, so
`pendingObligations M = []` for every `M`, and the theorem was true and
empty.

The R0–R5 ladder (`spec/t4-obligation-design-2026-07.md`) closed that:

1. `Term.boxed` — the obligation-carrying constructor (R1–R3). `Deriv.boxI`
   used to conclude at `Term.app`, so obligations never inhabited syntax.
2. `discharge-β` in `Reduce.lean` (R4) — a redex that DESTROYS a box.
3. `pendingObligations`' base case (R5, below) — a box contributes its own
   obligation, so the list can be non-empty.

`pendingObligations_eq_nil`, which proved the vacuity, is now FALSE and has
been deleted; `pendingObligations_ne_nil` refutes it in place. Its own
docstring had pre-registered this: "this lemma MUST break — its deletion is
the signal that T4 has acquired content."

The non-introduction direction proven here becomes one inequality of the
full multiset accounting
`obligations(M') = obligations(M) − discharged + introduced`.

The case-analysis machinery below (substAt subset lemma, per-redex
membership arithmetic) was retained across the ladder on the prediction
that the real proof would reuse it verbatim. It did: the cases needed
CONTENT for the new redex, not rewriting.
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
  -- THE BASE CASE. `box_O(M, N)` contributes its own obligation. Until R5
  -- this recursed without contributing `o`, which is exactly why
  -- `pendingObligations` was provably the constant `[]` and T4 was a real
  -- induction over a vacuous statement.
  | Term.boxed o m n            => o :: (pendingObligations m ++ pendingObligations n)
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
  | Term.saysBind _ s b          => pendingObligations s ++ pendingObligations b
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
  | boxed _ _ _ ihM ihπ => simp [shift, pendingObligations, ihM, ihπ]
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
  | saysBind _ _ _ ihS ihB => simp [shift, pendingObligations, ihS, ihB]
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
  | boxed ob m π ihM ihπ =>
    -- Now that `boxed` CONTRIBUTES its obligation, the membership splits
    -- three ways rather than two: `o` may be the box's own `ob`, or come
    -- from either sub-term. The `ob` case is new and is the whole point --
    -- substitution cannot change a box's own obligation, so it lands on
    -- the left immediately.
    intro value depth o hmem
    have hmem' : o ∈ ob :: (pendingObligations (substAt m value depth) ++
                            pendingObligations (substAt π value depth)) := hmem
    rcases List.mem_cons.mp hmem' with hOb | hRest
    · left
      show o ∈ ob :: (pendingObligations m ++ pendingObligations π)
      exact List.mem_cons.mpr (Or.inl hOb)
    · rcases List.mem_append.mp hRest with hM | hπ
      · rcases ihM value depth o hM with h | h
        · left
          show o ∈ ob :: (pendingObligations m ++ pendingObligations π)
          exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        · right; exact h
      · rcases ihπ value depth o hπ with h | h
        · left
          show o ∈ ob :: (pendingObligations m ++ pendingObligations π)
          exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h)))
        · right; exact h
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
  | saysBind _ s b ihS ihB =>
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

The proof is a term induction over `M` (the 2026-07 CONGRUENCE rules
make `step` recurse into elimination positions, so the subterm
induction hypotheses carry the ξ-cases). Head-redex arms use
`pendingObligations_substAt_subset` for the four substitution-style
redexes (β, case, letTensor, letSays) and direct list-membership
arithmetic for the rearrangement redexes (delegate, fst/snd,
sfExtract); ξ-arms map the reduced component's membership through the
induction hypothesis and pass the untouched components through
unchanged. The 14 value/frozen outer constructors contradict the
`step M = some M'` hypothesis. -/

/-- T4 — Reduction never introduces a new obligation. CAVEAT: vacuous
until the calculus has an obligation-carrying constructor — both sides
of the implication range over `pendingObligations _ = []` (see
`pendingObligations_eq_nil` and the module docstring). -/
theorem t4_no_new_obligation
    (M M' : Term) (h : step M = some M') :
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M := by
  revert M'
  induction M with
  | var _ => intro M' h; simp [step] at h
  | lam _ _ _ => intro M' h; simp [step] at h
  | app f x ihF _ =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- β: f = lam _ body, M' = subst body x. Every obligation of the
      -- substitution result was in the body or in the argument.
      simp only [Option.some.injEq] at h
      subst h
      rcases pendingObligations_substAt_subset _ _ _ o hmem with hB | hX
      · exact List.mem_append.mpr (Or.inl hB)
      · exact List.mem_append.mpr (Or.inr hX)
    · -- ξ-app: the argument passes through; the function position maps
      -- through the induction hypothesis.
      cases hf : step f with
      | none => simp [hf] at h
      | some f' =>
        simp [hf] at h
        subst h
        rcases List.mem_append.mp hmem with hF | hX
        · exact List.mem_append.mpr (Or.inl (ihF f' hf o hF))
        · exact List.mem_append.mpr (Or.inr hX)
  | sign _ _ _ _ => intro M' h; simp [step] at h
  | verify _ _ _ _ => intro M' h; simp [step] at h
  | delegate m n ihM ihN =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- delegate-β: M' = sign (acting p q) inner sig'; the surviving
      -- obligations are exactly the right-hand sign's.
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_append.mpr (Or.inr hmem)
    · -- ξ-delegate (right): left is a sign and passes through.
      cases hn : step n with
      | none => simp [hn] at h
      | some n' =>
        simp [hn] at h
        subst h
        rcases List.mem_append.mp hmem with hM | hN
        · exact List.mem_append.mpr (Or.inl hM)
        · exact List.mem_append.mpr (Or.inr (ihN n' hn o hN))
    · -- ξ-delegate (left): right passes through.
      cases hm : step m with
      | none => simp [hm] at h
      | some m' =>
        simp [hm] at h
        subst h
        rcases List.mem_append.mp hmem with hM | hN
        · exact List.mem_append.mpr (Or.inl (ihM m' hm o hM))
        · exact List.mem_append.mpr (Or.inr hN)
  | attenuate _ _ _ => intro M' h; simp [step] at h
  | discharge m p ihm _ =>
      -- No longer irreducible: R4 gave discharge a redex, so T4's own
      -- theorem now has real content in this case.
      intro M' h o hmem
      unfold step at h
      split at h
      · -- discharge-beta: M = discharge (boxed ob inner ev) p, M' = inner.
        --
        -- THIS is the case T4 exists for, and as of R5 it finally has
        -- content. The redex's obligation list is
        --   ob :: (pendingObligations inner ++ pendingObligations ev)
        -- and the contractum's is just `pendingObligations inner`. So the
        -- step DISCHARGES `ob` -- it disappears -- and introduces nothing.
        -- Every obligation of the result was already an obligation of the
        -- redex, one `cons` deeper. That is exactly the direction
        -- t4_no_new_obligation claims, now asserted about a rule that can
        -- fire and a list that can be non-empty.
        simp only [Option.some.injEq] at h
        subst h
        exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hmem)))
      · -- xi-discharge.
        cases hm : step m with
        | none => simp [hm] at h
        | some m' =>
            simp [hm] at h
            subst h
            exact ihm m' hm o hmem
  | liftLabel _ _ _ => intro M' h; simp [step] at h
  | boxed _ _ _ _ _ => intro M' h; simp [step] at h
  | declassify _ _ _ _ _ => intro M' h; simp [step] at h
  | now _ => intro M' h; simp [step] at h
  | withinIntro _ _ _ => intro M' h; simp [step] at h
  | pair _ _ _ _ => intro M' h; simp [step] at h
  | fst a ih =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- and-Eₗ-β: a = pair u v, M' = u.
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_append.mpr (Or.inl hmem)
    · -- ξ-fst: pendingObligations (fst X) = pendingObligations X.
      cases ha : step a with
      | none => simp [ha] at h
      | some a' =>
        simp [ha] at h
        subst h
        exact ih a' ha o hmem
  | snd a ih =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- and-Eᵣ-β: a = pair u v, M' = v.
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_append.mpr (Or.inr hmem)
    · -- ξ-snd.
      cases ha : step a with
      | none => simp [ha] at h
      | some a' =>
        simp [ha] at h
        subst h
        exact ih a' ha o hmem
  | inl _ _ _ => intro M' h; simp [step] at h
  | inr _ _ _ => intro M' h; simp [step] at h
  | case s l r ihS _ _ =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- or-E-β (inl): M' = subst l a. The scrutinee's payload a and
      -- the taken branch l both sit inside (S ++ L) ++ R.
      simp only [Option.some.injEq] at h
      subst h
      rcases pendingObligations_substAt_subset _ _ _ o hmem with hL | hA
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hL)))
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hA)))
    · -- or-E-β (inr): M' = subst r a.
      simp only [Option.some.injEq] at h
      subst h
      rcases pendingObligations_substAt_subset _ _ _ o hmem with hR | hA
      · exact List.mem_append.mpr (Or.inr hR)
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hA)))
    · -- ξ-case: branches pass through; the scrutinee maps through
      -- the induction hypothesis.
      cases hs : step s with
      | none => simp [hs] at h
      | some s' =>
        simp [hs] at h
        subst h
        rcases List.mem_append.mp hmem with hSL | hR
        · rcases List.mem_append.mp hSL with hS | hL
          · exact List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inl (ihS s' hs o hS))))
          · exact List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inr hL)))
        · exact List.mem_append.mpr (Or.inr hR)
  | tensorIntro _ _ _ _ => intro M' h; simp [step] at h
  | letTensor s b ihS _ =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- tensor-E-β: M' = subst (subst b (shift a 1 0)) bb. The
      -- `shift a 1 0` is a no-op on pendingObligations (it only
      -- renumbers free variables), so the membership reasoning is
      -- identical to the un-shifted version.
      simp only [Option.some.injEq] at h
      subst h
      rcases pendingObligations_substAt_subset _ _ _ o hmem with hBodyA | hB
      · rcases pendingObligations_substAt_subset _ _ _ o hBodyA with hBody | hA
        · exact List.mem_append.mpr (Or.inr hBody)
        · rw [pendingObligations_shift] at hA
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hA)))
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hB)))
    · -- ξ-lettensor.
      cases hs : step s with
      | none => simp [hs] at h
      | some s' =>
        simp [hs] at h
        subst h
        rcases List.mem_append.mp hmem with hS | hB
        · exact List.mem_append.mpr (Or.inl (ihS s' hs o hS))
        · exact List.mem_append.mpr (Or.inr hB)
  | saysBind p s b ihS _ =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- s = sign p' m sig; the head rule guards on p = p'.
      split at h
      · -- says-extract-β: M' = subst b m.
        simp only [Option.some.injEq] at h
        subst h
        rcases pendingObligations_substAt_subset _ _ _ o hmem with hB | hM
        · exact List.mem_append.mpr (Or.inr hB)
        · exact List.mem_append.mpr (Or.inl hM)
      · -- p ≠ p': step returned none — contradiction.
        simp at h
    · -- ξ-letsays.
      cases hs : step s with
      | none => simp [hs] at h
      | some s' =>
        simp [hs] at h
        subst h
        rcases List.mem_append.mp hmem with hS | hB
        · exact List.mem_append.mpr (Or.inl (ihS s' hs o hS))
        · exact List.mem_append.mpr (Or.inr hB)
  | letSays p s b ihS _ =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- s = sign p' m sig; the head rule guards on p = p'.
      split at h
      · -- says-extract-β: M' = subst b m.
        simp only [Option.some.injEq] at h
        subst h
        rcases pendingObligations_substAt_subset _ _ _ o hmem with hB | hM
        · exact List.mem_append.mpr (Or.inr hB)
        · exact List.mem_append.mpr (Or.inl hM)
      · -- p ≠ p': step returned none — contradiction.
        simp at h
    · -- ξ-letsays.
      cases hs : step s with
      | none => simp [hs] at h
      | some s' =>
        simp [hs] at h
        subst h
        rcases List.mem_append.mp hmem with hS | hB
        · exact List.mem_append.mpr (Or.inl (ihS s' hs o hS))
        · exact List.mem_append.mpr (Or.inr hB)
  | sfExtract m ih =>
    intro M' h o hmem
    unfold step at h
    split at h
    · -- sf-extract-β: M' = inner, and
      -- pendingObligations (sfExtract (sign _ inner _)) = pendingObligations inner.
      simp only [Option.some.injEq] at h
      subst h
      exact hmem
    · -- ξ-sfextract.
      cases hm : step m with
      | none => simp [hm] at h
      | some m' =>
        simp [hm] at h
        subst h
        exact ih m' hm o hmem

/-- T4 — Obligation soundness statement (non-introduction direction).
Kept as `abbrev` aliasing the proved theorem's statement. NO LONGER
VACUOUS as of R5: `pendingObligations` can be non-empty (see
`pendingObligations_ne_nil`), so this quantifies over a list that can
actually have members. -/
abbrev T4_ObligationSoundnessStatement : Prop :=
  ∀ (M M' : Term), step M = some M' →
    ∀ (o : Obligation),
      o ∈ pendingObligations M' → o ∈ pendingObligations M

/-! ## The vacuity, REFUTED.

The lemma that used to live here -- `pendingObligations_eq_nil`, proving
`pendingObligations M = []` for every `M` -- is now FALSE, and its own
docstring predicted that:

  "When Phase 2 adds an obligation-carrying constructor, this lemma MUST
   break -- its deletion is the signal that T4 has acquired content, and
   the ledger's T4 witness (a term with non-empty obligations) becomes
   satisfiable."

R5 added the obligation-carrying constructor's base case, so the lemma
broke exactly as pre-registered. Deleting it is the point, not collateral
damage; leaving a weakened version would defeat the purpose.

What replaces it is the refutation: an explicit term whose obligation list
is NON-EMPTY. Before this ladder no such term could be written, which is
what made T4's ~180-line induction quantify over the empty list. The
non-vacuity WITNESS the ledger gates on lives in `DLC/Witness/T4.lean`;
this is the minimal in-file counterexample. -/

/-- `pendingObligations` is NOT constantly empty. Direct refutation of the
deleted `pendingObligations_eq_nil`: a box carries its own obligation. -/
theorem pendingObligations_ne_nil :
    pendingObligations
      (Term.boxed Obligation.top (Term.var 0) (Term.var 1)) ≠ [] := by
  simp [pendingObligations]


end DLC
