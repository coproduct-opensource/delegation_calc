import DLCD.MultiDecree
import DLCD.CorrespondenceConsensus

namespace DLCD.TransportConsensus

open Aeneas Aeneas.Std Result
open dlc_d_rsm

/-! ## LawfulBEq for the generated `dlc_core.rsm.Command` AST.

`CorrespondenceConsensus.decided_square` decodes `consensus.decided votes v` to a
`List.countP (· == some v)` majority, where `==` is the FunsExternal-derived
structural `BEq` on `dlc_core.rsm.Command`. To route that operational count into
the hand `DLCD.agreement` (which keys quorum membership on propositional
`= some v`), we need `eq_of_beq : (c == v) = true → c = v` — i.e. `LawfulBEq` for
the derived structural equality. No `deriving LawfulBEq` handler exists, so we
construct it, leaves first (each Aeneas scalar/`Vec`/`Array` field already carries
`LawfulBEq`), in the FunsExternal `deriving BEq` order.

For the small leaf types a single `simp_all` with the type's own projection
(`@BEq.beq _ instBEqX = instBEqX.beq`, definitionally `rfl`) reduces the goal; leaf
`==` at scalar/`Vec` fields keeps its own `LawfulBEq`. For the large recursive
`Prop` and `Term` (14 / 27 constructors) the derived beq is *self-referential*, so
`simp [instBEqX.beq]` loops on the constructor match; there we split the beq by
defeq with `Bool.and_eq_true_iff` (which does NOT unfold it) and discharge each
field with its own `eq_of_beq` (leaf / already-established predecessor) or with the
induction hypothesis (recursive field). -/

/-- Per-field closer for the recursive AST types: after `congr 1` each field goal
`xᵢ = yᵢ` is closed by the field's own `eq_of_beq` (leaf / predecessor — the split
hyp is defeq to `(xᵢ == yᵢ) = true`) or by the induction hypothesis. -/
local macro "close_ast_fields" : tactic =>
  `(tactic| (first | exact eq_of_beq (by assumption) | (apply_assumption <;> assumption)))

/-- Diagonal (same-constructor) `eq_of_beq` closer: split `h`'s derived beq into
per-field conjuncts by defeq, then `congr 1` and discharge each field. Handles
arity 1–3 (the `Term` max), both associativities of the 3-way `&&`. -/
local macro "close_ast_diagonal" : tactic =>
  `(tactic| (first
    | (congr 1 <;> close_ast_fields)
    | (obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp ‹(_ : Bool) = true›
       congr 1 <;> close_ast_fields)
    | (obtain ⟨h1, hb⟩ := Bool.and_eq_true_iff.mp ‹(_ : Bool) = true›
       obtain ⟨h2, h3⟩ := Bool.and_eq_true_iff.mp hb; congr 1 <;> close_ast_fields)
    | (obtain ⟨ha, h3⟩ := Bool.and_eq_true_iff.mp ‹(_ : Bool) = true›
       obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp ha; congr 1 <;> close_ast_fields)))

/-- Per-field `rfl` (reflexivity of the derived beq): each `(xᵢ == xᵢ) = true`
is `beq_self_eq_true` (leaf / predecessor `ReflBEq`) or the induction hypothesis. -/
local macro "close_ast_refl" : tactic =>
  `(tactic| (first
    | rfl
    | (first | exact beq_self_eq_true _ | assumption)
    | (rename_i x; exact beq_self_eq_true x)
    | (refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩ <;>
        (first | exact beq_self_eq_true _ | assumption))
    | (refine Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩ <;>
        (first | exact beq_self_eq_true _ | assumption))
    | (refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩ <;>
        (first | exact beq_self_eq_true _ | assumption))))

instance : LawfulBEq dlc_core.time.TimeBound where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      simp_all only [show (BEq.beq (α := dlc_core.time.TimeBound)) = instBEqTimeBound.beq from rfl,
        instBEqTimeBound.beq, Bool.and_eq_true, beq_iff_eq, dlc_core.time.TimeBound.mk.injEq]
  rfl {a} := by
    cases a <;>
      simp_all only [show (BEq.beq (α := dlc_core.time.TimeBound)) = instBEqTimeBound.beq from rfl,
        instBEqTimeBound.beq, Bool.and_eq_true, beq_self_eq_true, and_self]

instance : LawfulBEq dlc_core.obligation.DpBudget where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      simp_all only [show (BEq.beq (α := dlc_core.obligation.DpBudget)) = instBEqDpBudget.beq from rfl,
        instBEqDpBudget.beq, Bool.and_eq_true, beq_iff_eq, dlc_core.obligation.DpBudget.mk.injEq]
  rfl {a} := by
    cases a <;>
      simp_all only [show (BEq.beq (α := dlc_core.obligation.DpBudget)) = instBEqDpBudget.beq from rfl,
        instBEqDpBudget.beq, Bool.and_eq_true, beq_self_eq_true, and_self]

instance : LawfulBEq dlc_core.principal.Principal where
  eq_of_beq {a b} h := by
    induction a generalizing b <;> cases b <;>
      (first | rfl | exact absurd ‹(_ : Bool) = true› Bool.false_ne_true | close_ast_diagonal)
  rfl {a} := by induction a <;> close_ast_refl

instance : LawfulBEq dlc_core.syntax.Signature where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      simp_all only [show (BEq.beq (α := dlc_core.syntax.Signature)) = instBEqSignature.beq from rfl,
        instBEqSignature.beq, Bool.and_eq_true, beq_iff_eq, dlc_core.syntax.Signature.mk.injEq]
  rfl {a} := by
    cases a <;>
      simp_all only [show (BEq.beq (α := dlc_core.syntax.Signature)) = instBEqSignature.beq from rfl,
        instBEqSignature.beq, Bool.and_eq_true, beq_self_eq_true, and_self]

instance : LawfulBEq dlc_core.obligation.Obligation where
  eq_of_beq {a b} h := by
    induction a generalizing b <;> cases b <;>
      (first | rfl | exact absurd ‹(_ : Bool) = true› Bool.false_ne_true | close_ast_diagonal)
  rfl {a} := by induction a <;> close_ast_refl

instance : LawfulBEq dlc_core.syntax.Prop where
  eq_of_beq {a b} h := by
    induction a generalizing b <;> cases b <;>
      (first | rfl | exact absurd ‹(_ : Bool) = true› Bool.false_ne_true | close_ast_diagonal)
  rfl {a} := by induction a <;> close_ast_refl

instance : LawfulBEq dlc_core.syntax.Term where
  eq_of_beq {a b} h := by
    induction a generalizing b <;> cases b <;>
      (first | rfl | exact absurd ‹(_ : Bool) = true› Bool.false_ne_true | close_ast_diagonal)
  rfl {a} := by induction a <;> close_ast_refl

instance : LawfulBEq dlc_core.rsm.Command where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      simp_all only [show (BEq.beq (α := dlc_core.rsm.Command)) = instBEqCommand.beq from rfl,
        instBEqCommand.beq, Bool.and_eq_true, beq_iff_eq, dlc_core.rsm.Command.mk.injEq]
  rfl {a} := by
    cases a <;>
      simp_all only [show (BEq.beq (α := dlc_core.rsm.Command)) = instBEqCommand.beq from rfl,
        instBEqCommand.beq, Bool.and_eq_true, beq_self_eq_true, and_self]

/-! # DLC-D Phase R2.4b — TRANSPORT (consensus tree): pulling CONSENSUS AGREEMENT
back to the deployed Rust runtime.

Companion to `DLCD.Transport` (the `dlc_core`-tree transport capstone). That module
deferred the consensus transport because its square lives over the SECOND generated
tree (`dlc_d_rsm`, in `DLCD.CorrespondenceConsensus`), which cannot co-import with the
`dlc_core` tree (`@[discriminant isize]` name collision). This module is rooted on the
`dlc_d_rsm` tree instead, and spends `CorrespondenceConsensus.decided_square` — the
proven refinement `consensus.decided votes v = ok (decide (|votes| < 2·#{votes = v}))`
— to transport single-decree AGREEMENT to the runtime.

`rust_consensus_agreement`: if the deployed `consensus.decided` engine certifies BOTH
`v₁` and `v₂` as decided over the same ballot (each returning `ok true`), then
`v₁ = v₂`. This is exactly the hand safety metatheorem `DLCD.agreement` ("at most one
value is decided") realized on the executable engine. The proof spends `decided_square`
to turn each `ok true` into a strict-majority count, and closes by the single-ballot
quorum-intersection fact `countP_add_le_length`: two disjoint predicates over one list
cannot both exceed half its length (the `Finset` quorum-intersection of `DLCD.agreement`
specialized to the runtime's list-of-votes representation — a ballot casts at most one
value per replica, so `{votes = v₁}` and `{votes = v₂}` are disjoint when `v₁ ≠ v₂`).
The disjointness step is where the derived-`BEq` `LawfulBEq` above is spent: `o == some v`
must imply `o = some v` to intersect the two majorities.

Partial-correctness / honest fence: conditioned on the Rust op returning `ok true`
(`consensus.decided` counts votes with a `U32` accumulator; the `hquorum` premises are the
same honest no-overflow fences `decided_square` carries). Non-vacuous: the conclusion is a
real command equality `v₁ = v₂` (not `x = x`), routed through a real square; `decided_witness`
below exhibits a concrete ballot on which `consensus.decided` genuinely returns `ok true`, so
the premise class is inhabited. No `sorry`, no `axiom`, no `native_decide`; footprint is
`[propext, Classical.choice, Quot.sound]`.

## R2.4b — the other two R2.4a deferrals, ASSESSED (verdict: both model-level)

* **Fair-scheduling liveness** (`Liveness.command_eventually_written`,
  `MultiDecreeLiveness.fair_quorum_decides` / `…_committed`). MODEL-LEVEL. The
  *operational* delivery-progress core — that ONE delivery step of the deployed
  engine advances the decoded replica exactly as the hand `deliver` — is already
  transported by `DLCD.Transport.rust_deliver_correct` (via `deliver_square`), and
  every per-step hand fact (`deliver_applied`, and hence the single-replica
  `command_eventually_applied`, which needs NO fairness) rides on it. The
  fair-scheduling WRAPPER does not: it quantifies over `FailureBudget.fairDelivery`
  and the abstract `SlotSchedule`, and `fairDelivery = true` is a HYPOTHESIS on the
  run (the FLP-forced external assumption), not a property any `rsm` op computes —
  there is no `schedule`/`fair` transition to route a square through. Forcing a
  `rust_*` here would fake a runtime witness for an environment assumption; honest
  scope keeps it model-level.

* **CALM lattice metatheorem** (`Calm.coordination_free_convergence`). MODEL-LEVEL.
  It is stated over an ABSTRACT `[SemilatticeSup L]` — a property of the order
  relation (`merge` is the join of a `foldl ⊔`), with no `rsm` operation to refine.
  Its RSM-level runtime content IS `DLCD.Transport.rust_replicas_converge` (already
  landed, via `apply_prefix_square`): two Rust replicas folding the same committed
  prefix decode to equal stores. The abstract semilattice algebra beyond that has no
  executable counterpart.

Net: of the three R2.4a consensus/liveness/CALM deferrals, exactly ONE
(consensus agreement) had transportable runtime content beyond what R2.4a already
shipped — closed here as `rust_consensus_agreement`. The other two are honestly
model-level (their runtime cores were already `rust_deliver_correct` /
`rust_replicas_converge`).

Prior art (from `Consensus.lean` / `MultiDecree.lean` headers; WebSearch budget exhausted):
- mwhittaker, *Single-Decree Paxos* — quorum decision + intersection:
  https://mwhittaker.github.io/blog/single_decree_paxos/
- Chand–Liu–Stoller, *Formal Verification of Multi-Paxos*, FM 2016 (per-slot single value):
  https://www3.cs.stonybrook.edu/~stoller/papers/fm2016.pdf
- García-Pérez et al., *Paxos Consensus, Deconstructed and Abstracted*, ESOP 2018:
  https://ilyasergey.net/assets/pdf/papers/paxos-deconstructed-esop18.pdf
- Aeneas (Ho–Protzenko–Fromherz, ICFP 2022): extracted-fn ↔ spec refinement.
  https://arxiv.org/abs/2206.07185
-/

/-- **Single-ballot quorum intersection (list form).** Two disjoint boolean predicates
over one list cannot each be satisfied by more than half its entries: their counts sum to
at most the length. This is the runtime-representation analogue of `Consensus.quorum_intersect`
(two majorities of `Fin n` overlap): a ballot is a *list* of votes, and `{· = v₁}` / `{· = v₂}`
are disjoint when `v₁ ≠ v₂`. Straight `countP` induction. -/
private theorem countP_add_le_length {α} (l : List α) (p q : α → Bool)
    (hdis : ∀ x ∈ l, ¬((p x = true) ∧ (q x = true))) :
    l.countP p + l.countP q ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => hdis x (List.mem_cons_of_mem a hx))
    have hd := hdis a (List.mem_cons_self ..)
    simp only [List.countP_cons, List.length_cons]
    by_cases hp : p a = true <;> by_cases hq : q a = true <;> simp_all <;> omega

/-- ★ **`rust_consensus_agreement` — consensus agreement, transported.** When the deployed
Rust `consensus.decided` engine certifies BOTH `v₁` and `v₂` as decided over the same ballot
`votes` (each call returning `ok true`), the two decided commands are EQUAL. This is the hand
safety metatheorem `DLCD.agreement` ("only one value can be chosen") realized on the executable
engine, spending `CorrespondenceConsensus.decided_square`. Conditioned on `ok true`
(partial-correctness) with the honest `U32` no-overflow fences of `decided_square`. -/
theorem rust_consensus_agreement
    (votes : Slice (Option dlc_core.rsm.Command)) (v₁ v₂ : dlc_core.rsm.Command)
    (hlen : votes.val.length < 2 ^ 32)
    (hq1 : 2 * (votes.val.countP (fun o => o == some v₁)) < 2 ^ 32)
    (hq2 : 2 * (votes.val.countP (fun o => o == some v₂)) < 2 ^ 32)
    (hd1 : consensus.decided votes v₁ = ok true)
    (hd2 : consensus.decided votes v₂ = ok true) :
    v₁ = v₂ := by
  -- Spend `decided_square`: each `ok true` decodes to a strict-majority vote count.
  have hm1 : votes.val.length < 2 * votes.val.countP (fun o => o == some v₁) :=
    of_decide_eq_true (Result.ok.inj
      ((CorrespondenceConsensus.decided_square votes v₁ hlen hq1).symm.trans hd1))
  have hm2 : votes.val.length < 2 * votes.val.countP (fun o => o == some v₂) :=
    of_decide_eq_true (Result.ok.inj
      ((CorrespondenceConsensus.decided_square votes v₂ hlen hq2).symm.trans hd2))
  -- Quorum intersection: if `v₁ ≠ v₂` the two majorities are disjoint, contradicting `hm₁/hm₂`.
  by_contra hne
  have hdis : ∀ o ∈ votes.val, ¬(((o == some v₁) = true) ∧ ((o == some v₂) = true)) := by
    rintro o _ ⟨ha, hb⟩
    exact hne (Option.some.inj ((eq_of_beq ha).symm.trans (eq_of_beq hb)))
  have hle := countP_add_le_length votes.val _ _ hdis
  omega

/-- ★★ **`rust_byz_agreement` — BYZANTINE consensus agreement, transported.** When
the deployed Rust `consensus.byz_decided` engine certifies BOTH `v₁` and `v₂` over
the same ballot at the `3·card > 2n` threshold (each `ok true`), the two decided
commands are EQUAL. The runtime image of `DLCD.ByzantineConsensus.byz_agreement`.

The honest-set `B` of the hand theorem does NOT appear here, and that is faithful,
not a shortcut: the runtime ballot is a `List (Option Command)` — one entry per
roster position — so "an honest replica votes at most once" is STRUCTURAL (each
slot holds one value). Two `> 2n/3` supermajorities for distinct values would have
to be disjoint (no slot holds both), and `2·(2n/3) > n`, so they cannot fit — the
same `byz_quorum_honest_intersect` pigeonhole, realized at the list level where the
one-vote invariant is free. Conditioned on `ok true` (partial-correctness) with the
`U32` no-overflow fences of `byz_decided_square`. -/
theorem rust_byz_agreement
    (votes : Slice (Option dlc_core.rsm.Command)) (v₁ v₂ : dlc_core.rsm.Command)
    (hlen : votes.val.length < 2 ^ 32)
    (hq2 : 2 * votes.val.length < 2 ^ 32)
    (hc1 : 3 * (votes.val.countP (fun o => o == some v₁)) < 2 ^ 32)
    (hc2 : 3 * (votes.val.countP (fun o => o == some v₂)) < 2 ^ 32)
    (hd1 : consensus.byz_decided votes v₁ = ok true)
    (hd2 : consensus.byz_decided votes v₂ = ok true) :
    v₁ = v₂ := by
  -- Spend `byz_decided_square`: each `ok true` decodes to a Byzantine supermajority.
  have hm1 : 2 * votes.val.length < 3 * votes.val.countP (fun o => o == some v₁) :=
    of_decide_eq_true (Result.ok.inj
      ((CorrespondenceConsensus.byz_decided_square votes v₁ hlen hc1 hq2).symm.trans hd1))
  have hm2 : 2 * votes.val.length < 3 * votes.val.countP (fun o => o == some v₂) :=
    of_decide_eq_true (Result.ok.inj
      ((CorrespondenceConsensus.byz_decided_square votes v₂ hlen hc2 hq2).symm.trans hd2))
  -- Byzantine quorum intersection at the list level: two `> 2n/3` supermajorities for
  -- distinct values are disjoint, and `2·(2n/3) > n` cannot fit — contradiction.
  by_contra hne
  have hdis : ∀ o ∈ votes.val, ¬(((o == some v₁) = true) ∧ ((o == some v₂) = true)) := by
    rintro o _ ⟨ha, hb⟩
    exact hne (Option.some.inj ((eq_of_beq ha).symm.trans (eq_of_beq hb)))
  have hle := countP_add_le_length votes.val _ _ hdis
  omega

/-! ## Non-vacuity: a concrete ballot on which the runtime engine decides. -/

namespace ConsensusTransportWitness

/-- A concrete command (real `Term` payload). -/
def c : dlc_core.rsm.Command := { payload := dlc_core.syntax.Term.Var 0#u32, cap := none }

/-- A three-vote ballot, all for `c` (a real strict majority: 3 > 3/2). -/
def votes : Slice (Option dlc_core.rsm.Command) :=
  ⟨[some c, some c, some c], by simp; scalar_tac⟩

private theorem hlen : votes.val.length < 2 ^ 32 := by simp [votes]

private theorem hq : 2 * (votes.val.countP (fun o => o == some c)) < 2 ^ 32 := by
  show 2 * (List.countP (fun o => o == some c) [some c, some c, some c]) < 2 ^ 32
  simp only [List.countP_cons, List.countP_nil, beq_self_eq_true, if_true]; decide

/-- **The runtime engine genuinely decides `c`.** `consensus.decided` returns `ok true` on
this concrete ballot — the operational premise of `rust_consensus_agreement` is inhabited, so
the transported agreement is non-vacuous (it fires on a real, computing input). -/
theorem decided_witness : consensus.decided votes c = ok true := by
  rw [CorrespondenceConsensus.decided_square votes c hlen hq]
  show ok (decide (List.length [some c, some c, some c]
      < 2 * List.countP (fun o => o == some c) [some c, some c, some c])) = ok true
  simp only [List.countP_cons, List.countP_nil, List.length_cons, List.length_nil,
    beq_self_eq_true, if_true]
  rfl

private theorem hq2 : 2 * votes.val.length < 2 ^ 32 := by simp [votes]

private theorem hc3 : 3 * (votes.val.countP (fun o => o == some c)) < 2 ^ 32 := by
  show 3 * (List.countP (fun o => o == some c) [some c, some c, some c]) < 2 ^ 32
  simp only [List.countP_cons, List.countP_nil, beq_self_eq_true, if_true]; decide

/-- **The runtime engine genuinely BYZANTINE-decides `c`.** All three vote for `c`,
and `2·3 < 3·3` (`6 < 9`) is a Byzantine supermajority — so `consensus.byz_decided`
returns `ok true`, inhabiting the operational premise of `rust_byz_agreement`. -/
theorem byz_decided_witness : consensus.byz_decided votes c = ok true := by
  rw [CorrespondenceConsensus.byz_decided_square votes c hlen hc3 hq2]
  show ok (decide (2 * List.length [some c, some c, some c]
      < 3 * List.countP (fun o => o == some c) [some c, some c, some c])) = ok true
  simp only [List.countP_cons, List.countP_nil, List.length_cons, List.length_nil,
    beq_self_eq_true, if_true]
  rfl

end ConsensusTransportWitness

end DLCD.TransportConsensus
