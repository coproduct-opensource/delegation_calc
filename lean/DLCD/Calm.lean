import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.List.Perm.Basic

/-! # DLC-D Phase 2.e — CALM: coordination-FREE convergence of the monotone fragment

This module proves, for a join-semilattice state, the **⇐ direction of the CALM
theorem operationally**: *monotone (join-with-delta) updates converge with NO
coordination* — no consensus, no total order, no quorum, no agreement. The only
hypothesis is that the two replicas absorbed the **same set of deltas**;
delivery order and duplication are irrelevant. It is the deliberate CONTRAST to
`DLCD.Consensus.replicas_converge_via_consensus`, which needs single-decree
agreement (a total order per slot) because the general/non-monotone case cannot
converge without coordination.

## The CALM theorem (prior art — web-searched 2026-07-22, URLs recorded)
- Hellerstein & Alvaro, **"Keeping CALM: When Distributed Consistency is Easy"**,
  CACM 2020 / arXiv:1901.01930. THE CALM theorem: *a problem has a consistent,
  COORDINATION-FREE distributed implementation iff it is monotone.* Monotone
  problems are "safe in the face of missing information" and proceed without
  coordination; non-monotone problems require coordination for consistency.
  https://arxiv.org/abs/1901.01930  https://arxiv.org/pdf/1901.01930
  https://cacm.acm.org/research/keeping-calm/
  https://dl.acm.org/doi/pdf/10.1145/3369736
- Gomes, Kleppmann, Mulligan & Beresford, **"Verifying Strong Eventual
  Consistency in Distributed Systems"**, OOPSLA 2017 (Isabelle/HOL). Identifies
  the **abstract convergence theorem** — a property of *order relations* — as
  "the essence of why SEC algorithms converge". The closest mechanized prior
  art; our `merge_le_iff` universal property + `merge_mem_invariant` is exactly
  this order-relation core specialized to a join-semilattice (a grow-only /
  observed-remove-set-style CRDT). https://martin.kleppmann.com/papers/crdt-isabelle-oopsla17.pdf
  AFP: https://www.isa-afp.org/browser_info/current/AFP/CRDT/document.pdf
- Ameloot, Neven & Van den Bussche, transducer-network proof of CALM (weak
  monotonicity ⇔ coordination-freeness): https://arxiv.org/pdf/1202.0242
- "Complete CALM: A Coordination Criterion for Specifications":
  https://arxiv.org/html/2602.09435v3  (PDF: https://arxiv.org/pdf/2602.09435)

## What is proved (the deliverable)
Over any `[SemilatticeSup L]`:
1. `applyδ (δ s) := s ⊔ δ` — a monotone update: absorbing a delta by join. It is
   automatically commutative, associative, idempotent (these are the sup laws).
2. `merge ds s := ds.foldl (· ⊔ ·) s` — fold a list/multiset of deltas by join.
3. `merge_le_iff` — the **universal property** (the abstract-convergence core):
   `merge ds s ≤ t ↔ s ≤ t ∧ ∀ x ∈ ds, x ≤ t`. `merge ds s` is the least upper
   bound of `{s} ∪ set(ds)` — so it is a *function of the SET of deltas alone*.
4. `merge_mem_invariant` — same delivered set ⇒ equal state (from 3 by
   antisymmetry). This is the master lemma; both of the next two are corollaries.
5. `merge_perm_invariant` — **order-independence** (reordering): `List.Perm` of
   deltas ⇒ equal state. Join is commutative+associative.
6. `merge_idempotent_dup` — **duplicate-insensitivity**: `merge (d::d::ds) s =
   merge (d::ds) s`, proved *directly* from `sup_idem` so idempotence is visibly
   load-bearing.
7. `coordination_free_convergence` — **THE THEOREM**. `r₁ = merge ds₁ s₀`,
   `r₂ = merge ds₂ s₀`, and *only* `∀ x, x ∈ ds₁ ↔ x ∈ ds₂` (same delivered
   SET) ⇒ `r₁ = r₂`. Read the hypotheses: NO quorum, NO agreement, NO ordering
   — the CALM "coordination-free" claim made literal.

## The right-reason bite — the CALM boundary made concrete
A NON-monotone update `overwrite v s := v` (last-writer-wins assignment, not a
join): `overwrite_noncomm` shows it does not commute, and
`overwrite_merge_diverges` exhibits two replicas that absorb the **same set**
`{0,1}` in different orders yet reach **different** states. So under the *very
same* set-equality hypothesis that makes the join-merge CONVERGE, the
non-monotone merge DIVERGES: monotonicity is load-bearing, order matters,
coordination is REQUIRED. That is the CALM boundary.

## Anti-vacuity witness (`Witness` namespace)
A concrete grow-only set `Finset ℕ` under `∪` (= `⊔`). Replica 1 absorbs
`[{1},{2},{1}]` (with a DUPLICATE `{1}`); replica 2 absorbs `[{2},{1}]`
(REORDERED, deduplicated). They provably converge — via
`coordination_free_convergence` — to `{1,2} ≠ ∅`. Reordering AND duplication are
genuinely present, and the converged value is non-trivial (the deltas really
did something).

## Honest fences
- **Lattice choice.** We take a Mathlib `[SemilatticeSup L]` typeclass parameter
  rather than DLC's `DLC.CoproductAlgebra.LawfulCLattice`. The latter mirrors the
  Rust `coproduct_algebra::Lattice` trait and its only lawful instance is the
  finite chain `Rank6`; it is not a generic reusable class and — decisively — the
  witness state `Finset ℕ` is a Mathlib `SemilatticeSup` but is *not* a
  `LawfulCLattice`. Mathlib's `⊔` gives `sup_comm`/`sup_assoc`/`sup_idem`/
  `sup_le_iff` and the `Finset`/`ℕ`/`Bool` instances for free. (`Rank6`'s
  `cjoin` is proved *equal* to Mathlib's `⊔` in `CoproductAlgebra.cjoin_eq_sup`,
  so this theorem transfers to `LawfulCLattice` types too, via that bridge.)
- **Scope.** This is the coordination-FREE convergence of the MONOTONE fragment
  — the CALM ⇐ direction, operationally. The full CALM *iff*-characterization
  (monotone ⟺ coordination-free, BOTH directions, quantified over a program
  syntax with a semantic monotonicity predicate) is a deeper Phase-2+ target;
  it is NOT claimed here. Contrast partner: `DLCD.Consensus.replicas_converge_
  via_consensus` earns convergence for the *general* (non-monotone) case, and it
  must invoke per-slot `agreement`/total order to do so — precisely the
  coordination this file shows the monotone fragment does without.
-/

namespace DLCD
namespace Calm

/-! ## 1. Monotone (join-with-delta) updates and the merge fold. -/

section Monotone

variable {L : Type*} [SemilatticeSup L]

/-- A **monotone update**: absorb a delta `δ` into state `s` by join. Automatically
commutative, associative, idempotent — these are the `SemilatticeSup` laws, not
extra hypotheses. This is the CALM "monotone" primitive. -/
def applyδ (δ s : L) : L := s ⊔ δ

/-- Fold a list (≈ multiset) of deltas into a state by join. The whole of a
replica's state as a function of the deltas it absorbed. -/
def merge (ds : List L) (s : L) : L := ds.foldl (· ⊔ ·) s

@[simp] theorem merge_nil (s : L) : merge [] s = s := rfl

/-- Absorbing one more delta at the front: `merge (d::ds) s = merge ds (s ⊔ d)`.
Holds definitionally (`foldl`). -/
theorem merge_cons (d : L) (ds : List L) (s : L) :
    merge (d :: ds) s = merge ds (s ⊔ d) := rfl

/-- **THE UNIVERSAL PROPERTY (abstract-convergence core).** `merge ds s` is the
least upper bound of `{s} ∪ set(ds)`: it is `≤ t` iff `s ≤ t` and every delta is
`≤ t`. This is the order-relation property Gomes–Kleppmann isolate as the essence
of convergence. Everything below is a corollary; in particular it exhibits
`merge ds s` as a function of the *set* of deltas, independent of order/count. -/
theorem merge_le_iff (ds : List L) (s t : L) :
    merge ds s ≤ t ↔ s ≤ t ∧ ∀ x ∈ ds, x ≤ t := by
  induction ds generalizing s with
  | nil => simp [merge]
  | cons d ds ih =>
      rw [merge_cons, ih]
      constructor
      · rintro ⟨hsd, hall⟩
        rw [sup_le_iff] at hsd
        refine ⟨hsd.1, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with h | h
        · subst h; exact hsd.2
        · exact hall x h
      · rintro ⟨hs, hall⟩
        refine ⟨sup_le hs (hall d (by simp)), ?_⟩
        intro x hx
        exact hall x (by simp [hx])

/-- The state dominates the initial state: `s ≤ merge ds s`. -/
theorem merge_ge (ds : List L) (s : L) : s ≤ merge ds s :=
  ((merge_le_iff ds s (merge ds s)).1 le_rfl).1

/-- Every absorbed delta is dominated by the merged state: `x ∈ ds → x ≤ merge ds s`. -/
theorem merge_mem_le (ds : List L) (s : L) {x : L} (hx : x ∈ ds) : x ≤ merge ds s :=
  ((merge_le_iff ds s (merge ds s)).1 le_rfl).2 x hx

/-- **THE MASTER LEMMA — set-invariance.** Two delta lists with the SAME
underlying set produce EQUAL merged state. Proof: each side is `≤` the other by
the universal property (same members ⇒ same upper-bound obligations), then
antisymmetry. This subsumes reordering and duplication in one stroke. -/
theorem merge_mem_invariant {ds₁ ds₂ : List L} (s : L)
    (h : ∀ x, x ∈ ds₁ ↔ x ∈ ds₂) : merge ds₁ s = merge ds₂ s := by
  apply le_antisymm
  · rw [merge_le_iff]
    exact ⟨merge_ge ds₂ s, fun x hx => merge_mem_le ds₂ s ((h x).1 hx)⟩
  · rw [merge_le_iff]
    exact ⟨merge_ge ds₁ s, fun x hx => merge_mem_le ds₁ s ((h x).2 hx)⟩

/-- **ORDER-INDEPENDENCE** (the key coordination-free property). Deltas delivered
in ANY order (a `List.Perm`) reach the same state — join is commutative and
associative. A permutation preserves membership, so this is `merge_mem_invariant`. -/
theorem merge_perm_invariant {ds₁ ds₂ : List L} (s : L)
    (h : List.Perm ds₁ ds₂) : merge ds₁ s = merge ds₂ s :=
  merge_mem_invariant s (fun _ => h.mem_iff)

/-- **DUPLICATE-INSENSITIVITY** (idempotence, made visibly load-bearing). A delta
delivered TWICE has the same effect as once — proved *directly* from `sup_idem`,
not via the set lemma, so the reader sees idempotence do the work:
`merge ds ((s ⊔ d) ⊔ d) = merge ds (s ⊔ d)`. -/
theorem merge_idempotent_dup (d : L) (ds : List L) (s : L) :
    merge (d :: d :: ds) s = merge (d :: ds) s := by
  simp only [merge_cons, sup_assoc, sup_idem]

/-- **THE COORDINATION-FREE CONVERGENCE THEOREM (the deliverable).** Two replicas
`r₁ = merge ds₁ s₀` and `r₂ = merge ds₂ s₀` that have absorbed the **same set of
deltas** reach EQUAL state. Read the hypotheses: the ONLY assumption relating the
replicas is `∀ x, x ∈ ds₁ ↔ x ∈ ds₂` — set-equality of the delivered deltas.
There is **no quorum, no agreement, no total order, no ordering assumption of any
kind**. This is the CALM ⇐ direction operationally: monotone ⇒ coordination-free
convergence. (Contrast `Consensus.replicas_converge_via_consensus`, whose
convergence must route through per-slot `agreement` / a total order.) -/
theorem coordination_free_convergence {ds₁ ds₂ : List L} (s₀ : L)
    (hset : ∀ x, x ∈ ds₁ ↔ x ∈ ds₂)
    {r₁ r₂ : L} (h₁ : r₁ = merge ds₁ s₀) (h₂ : r₂ = merge ds₂ s₀) :
    r₁ = r₂ := by
  rw [h₁, h₂]; exact merge_mem_invariant s₀ hset

end Monotone

/-! ## 2. The right-reason bite — a NON-monotone update DIVERGES (CALM boundary). -/

section Bite

variable {L : Type*}

/-- A **non-monotone** update: last-writer-wins assignment. It ignores the current
state entirely (`overwrite v s = v`) — the antithesis of a join, and NOT monotone. -/
def overwrite (v _s : L) : L := v

/-- Merge under overwrite: fold keeping the LAST delta. Order-sensitive by design. -/
def owMerge (ds : List L) (s : L) : L := ds.foldl (fun _ d => d) s

/-- **THE BITE (pointwise).** `overwrite` does not commute: applying deltas `v₁`
then `v₂` in the two orders gives `v₁` vs `v₂`, which differ. Concretely `0` and
`1` over `ℕ`. Non-monotone ⇒ order matters. -/
theorem overwrite_noncomm :
    ∃ (v₁ v₂ s : ℕ), overwrite v₁ (overwrite v₂ s) ≠ overwrite v₂ (overwrite v₁ s) :=
  ⟨0, 1, 0, by decide⟩

/-- **THE BITE (whole-merge, the CALM contrast).** Two replicas absorb the SAME
SET of deltas `{0,1}` in DIFFERENT orders — the *exact* hypothesis under which
the join-merge `coordination_free_convergence` proves EQUALITY — yet the
non-monotone `owMerge` reaches DIFFERENT states (`1` vs `0`). So monotonicity is
load-bearing: drop it and coordination becomes necessary. This is the CALM
boundary made concrete. -/
theorem overwrite_merge_diverges :
    ∃ (ds₁ ds₂ : List ℕ) (s : ℕ),
      (∀ x, x ∈ ds₁ ↔ x ∈ ds₂) ∧ owMerge ds₁ s ≠ owMerge ds₂ s := by
  refine ⟨[0, 1], [1, 0], 0, ?_, ?_⟩
  · intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · decide

end Bite

/-! ## 3. Anti-vacuity witness — a concrete grow-only set that PROVABLY converges. -/

namespace Witness

/-- The state lattice: a grow-only set of naturals under `∪` (= `⊔`). This is the
canonical G-Set CRDT; `Finset ℕ` is a Mathlib `SemilatticeSup`. -/
abbrev S := Finset ℕ

/-- The shared initial state: the empty set. -/
def s0 : S := ∅

/-- Delta A: add `1`. -/
def d1 : S := {1}
/-- Delta B: add `2`. -/
def d2 : S := {2}

/-- Replica 1's delivery: `[{1}, {2}, {1}]` — note the **DUPLICATE** `{1}`. -/
def ds1 : List S := [d1, d2, d1]

/-- Replica 2's delivery: `[{2}, {1}]` — **REORDERED** and deduplicated. -/
def ds2 : List S := [d2, d1]

/-- The two deliveries carry the SAME SET of deltas `{ {1}, {2} }`, despite the
duplicate and the reordering. This is the only hypothesis the convergence theorem
consumes. -/
theorem witness_same_set : ∀ x, x ∈ ds1 ↔ x ∈ ds2 := by
  intro x
  simp only [ds1, ds2, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h) <;> tauto
  · rintro (h | h) <;> tauto

/-- **CONVERGENCE, non-vacuously.** The two replicas — one with a duplicate, one
reordered — reach EQUAL state, routed through the coordination-free theorem. No
consensus, no order agreement invoked; only `witness_same_set`. -/
theorem witness_converge : merge ds1 s0 = merge ds2 s0 :=
  coordination_free_convergence s0 witness_same_set rfl rfl

/-- The converged value is the non-trivial `{1, 2}` — the deltas genuinely acted.
(Proved by `ext`/`simp` rather than `decide`: `Finset ℕ`'s `DecidableEq` reduces
through a `Quot` and gets stuck in the kernel — but it is still `[propext,
Classical.choice, Quot.sound]`-clean, no `native_decide`.) -/
theorem witness_converged_value : merge ds1 s0 = ({1, 2} : Finset ℕ) := by
  have hstep : merge ds1 s0 = ((s0 ⊔ d1) ⊔ d2) ⊔ d1 := rfl
  rw [hstep]
  ext a
  simp only [s0, d1, d2, Finset.sup_eq_union, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty, Finset.mem_insert]
  tauto

/-- ...and it is genuinely different from the initial state `∅` (non-vacuous). -/
theorem witness_nontrivial : merge ds1 s0 ≠ s0 := by
  rw [witness_converged_value]
  intro h
  have h1 : (1 : ℕ) ∈ ({1, 2} : Finset ℕ) := by simp
  rw [h] at h1
  simp [s0] at h1

/-- Duplication is really present: `ds1` is NOT duplicate-free (`{1}` appears twice). -/
theorem witness_has_duplicate : ¬ ds1.Nodup := by
  intro h
  simp only [ds1] at h
  rw [List.nodup_cons] at h
  exact h.1 (by simp)

/-- Reordering is really present: the two deliveries are NOT the same list
(different lengths). -/
theorem witness_reordered : ds1 ≠ ds2 := by
  intro h
  have hlen := congrArg List.length h
  simp only [ds1, ds2, List.length_cons, List.length_nil] at hlen
  omega

end Witness

end Calm
end DLCD
