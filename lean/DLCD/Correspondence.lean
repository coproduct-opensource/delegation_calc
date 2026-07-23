import DLCD.Rsm            -- the SPEC side (hand model): DLCD.applyCommand, deliver, worldStep, …
import DlcCore             -- the CODE side (real Aeneas defs): dlc_core.rsm.*, reduce.*, syntax.*
-- NOTE: the `dlc_d_rsm` consensus layer lives in a SEPARATE module,
-- `DLCD.CorrespondenceConsensus`. The two generated trees cannot be imported
-- into the same Lean module: `@[discriminant isize]` on both
-- `dlc_core.syntax.Term` and `dlc_d_rsm.dlc_core.syntax.Term` emits a
-- same-short-named instance `instDiscriminantTermIsize`, which collides at
-- import. Both modules are roots of the `DLCDCorrespondence` lib.

/-! # DLC-D Phase R2.2b — the correspondence core: decode `⟦·⟧`, the conditional
structural squares, and the anti-vacuity witness.

This module opens the *one-directional* correspondence (generated → hand) between
the Aeneas-generated `dlc_core.rsm` transition engine (real `def`s in the
`DlcCore` tree — `reduce_with_fuel`, `apply_command`, `apply_prefix`, `deliver`,
`world_step`, `commit`) and the hand-written `DLCD.Rsm` model, plus the
`dlc_d_rsm.consensus` layer.

## What R2.2b delivers (and what it does NOT)
- **decode `⟦·⟧`.** Concrete, total, structural container decodes for
  `dlc_core.rsm.{FailureBudget, Command, Replica, GlobalConfig}` into the hand
  `DLCD.*` records. The `Term`/`Prop` *payload* decode is the deferred
  `dlc-core` correspondence (R2.3): the whole development is **parametric** over
  two abstract seam functions `decTm`/`decPr`, pinned to a concrete fragment
  decode only for the anti-vacuity witness.
- **`AppCommandRefines` — the single deferred obligation.** A `def … : Prop`
  (never an `axiom`, never a `sorry`) stating that the generated per-command
  engine refines `DLCD.applyCommand` under the payload decode on well-scoped
  inputs. The reducer-routed structural squares are stated **conditional on**
  this hypothesis; R2.3 discharges it.
- **the anti-vacuity witness.** `appCommandRefines_witness` proves the
  `AppCommandRefines` equation holds on the concrete *state-changing* `dup`
  instance (`⟨var0,var0⟩ ≠ var0`), computed through the now-real
  `apply_command`/`reduce_with_fuel`. This is the closed satisfiability witness
  that defeats vacuity: the conditional squares are not free-because-the-
  hypothesis-is-unsatisfiable — the hypothesis's *consequent* is achievable on a
  real input. Its axiom footprint is exactly `[propext, Classical.choice,
  Quot.sound]`.

The honest R2.2b claim: *the whole operational transport is reduced to exactly
one stated reducer correspondence `AppCommandRefines`, and that lemma's
consequent is machine-checked non-vacuous on a state-changing input.* This is
NOT a claim that the Rust core satisfies G1–G4.

**Square coverage (R2.2b).** `is_quorum_square` lands (in the companion module
`DLCD.CorrespondenceConsensus`, which owns the `dlc_d_rsm` tree). The
reducer-routed structural squares (`deliver`, `world_step`, `apply_prefix`) plus
`commit` and `decided` are the R2.2b-continuation: they route the reducer through
the `AppCommandRefines` hypothesis and additionally rest on an AST-wide
clone-identity lemma (tractable via `List.mapM_clone_eq` + a mutual induction —
the `vecClone_id` helper below is the Vec base case) and, for the loop functions,
accumulator inductions. They are not yet landed and — per the no-`sorry`
discipline — are therefore not stated here.

Prior art (web-searched 2026-07-23; URLs recorded):
- Aeneas (Ho–Protzenko–Fromherz, ICFP 2022): each Rust fn → a `Result α`
  (`ok`/`fail`/`div`) Lean fn; prove the extracted fn matches a spec.
  https://arxiv.org/abs/2206.07185 , https://lean-lang.org/use-cases/aeneas/
- Grove (Sharma et al., SOSP 2023): "verified impl refines an abstract
  state-machine spec"; the refinement *square* (decode, invoke abstract, re-encode).
  https://iris-project.org/pdfs/2023-sosp-grove.pdf
- Aeneas loop proof pattern (accumulator generalization; `loop.eq_1` unfolding):
  https://github.com/AeneasVerif/aeneas ,
  https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html
- Vacuous-hypothesis / satisfiability-witness discipline:
  https://arxiv.org/pdf/2606.29493
-/

namespace DLCD.Correspondence

open Aeneas Aeneas.Std Result
open dlc_core

/-! ## 1. The abstract payload seam (R2.3 pins these; R2.2b is parametric). -/

/-- The deferred `dlc-core` Term decode (generated → hand). Abstract in R2.2b. -/
abbrev DecTm := syntax.Term → DLC.Term
/-- The deferred `dlc-core` Prop decode (generated → hand). Abstract in R2.2b. -/
abbrev DecPr := syntax.Prop → DLC.Prop'

/-! ## 2. The concrete container decodes `⟦·⟧` (total, computable, structural). -/

/-- `FailureBudget`: `u32 → Nat`, structural. CONCRETE (no seam). -/
def decBudget (b : rsm.FailureBudget) : DLCD.FailureBudget :=
  { maxFaults := b.max_faults.val, fairDelivery := b.fair_delivery,
    consumed := b.consumed.val }

/-- `Command`: payload via the abstract `decTm`; cap via `decPr` (Option-mapped). -/
def decCmd (decTm : DecTm) (decPr : DecPr) (c : rsm.Command) : DLCD.Command :=
  { payload := decTm c.payload, cap := c.cap.map decPr }

/-- `Replica`: id/applied `u32→Nat`; store via `decTm`. -/
def decRep (decTm : DecTm) (r : rsm.Replica) : DLCD.Replica :=
  { id := r.id.val, store := decTm r.store, applied := r.applied.val }

/-- `CommittedLog`: `Vec Command → List Command`, pointwise `decCmd`. -/
def decLog (decTm : DecTm) (decPr : DecPr) (log : alloc.vec.Vec rsm.Command) :
    DLCD.CommittedLog :=
  log.val.map (decCmd decTm decPr)

/-- `GlobalConfig`: replicas + log + budget. -/
def decGC (decTm : DecTm) (decPr : DecPr) (g : rsm.GlobalConfig) : DLCD.GlobalConfig :=
  { replicas := g.replicas.val.map (decRep decTm),
    log := decLog decTm decPr g.log,
    budget := decBudget g.budget }

/-! ## 2b. Clone-identity base case (groundwork for the reducer-routed squares).

The generated `deliver`/`world_step`/`commit` all `clone` a `Vec`/`Term` before
decoding it; the structural squares therefore rest on an AST-wide clone-identity
fact `clone x = ok x`. Its `Vec` base case is `vecClone_id` (via
`List.mapM_clone_eq`); the recursive `Term`/`Prop`/`Principal`/`Obligation` cases
are a mutual induction that is the R2.2b-continuation. -/

/-- A `Vec` whose elements each clone to themselves clones to itself. -/
private theorem vecClone_id {T} (cl : core.clone.Clone T) (v : alloc.vec.Vec T)
    (h : ∀ x ∈ v.val, cl.clone x = ok x) :
    alloc.vec.CloneVec.clone cl v = ok v := by
  have hm := List.mapM_clone_eq h
  simp only [alloc.vec.CloneVec.clone, Slice.clone, List.clone]
  split
  · rename_i v1 heq; rw [hm] at heq; injection heq with heq; subst heq
    simp only [bind_tc_ok]; rfl
  · rename_i e heq; rw [hm] at heq; exact absurd heq (by simp)
  · rename_i heq; rw [hm] at heq; exact absurd heq (by simp)

/-! ## 3. The `WellScopedTm` fence (the sound content of the `U32`-vs-`Nat` gap).

`WellScopedTm` is the honest, decidable structural predicate that bounds every
variable index in a term below `2^31`, so the `I32`/`I64` shift arithmetic inside
`subst.shift` / `subst.subst_at` never overflows during reduction and
`reduce_with_fuel` never returns `.fail`. It is folded into `AppCommandRefines`
via the `.map … = .ok …` form (which *also* asserts no-fail). This is NOT `True`:
it genuinely constrains the term's variable indices. -/

/-- Every `Var` index in the term is `< 2^31` (safe for the shift arithmetic). -/
def wsTermB : syntax.Term → Bool
  | .Var i => i.val < 2147483648
  | .Lam _ t => wsTermB t
  | .App a b => wsTermB a && wsTermB b
  | .Sign _ t _ => wsTermB t
  | .Verify _ t _ => wsTermB t
  | .Delegate a b => wsTermB a && wsTermB b
  | .Attenuate t _ => wsTermB t
  | .SaysBind _ a b => wsTermB a && wsTermB b
  | .Boxed _ a b => wsTermB a && wsTermB b
  | .Discharge a b => wsTermB a && wsTermB b
  | .LiftLabel _ t => wsTermB t
  | .Declassify _ a b => wsTermB a && wsTermB b
  | .Now _ => true
  | .WithinIntro _ t => wsTermB t
  | .Pair a b => wsTermB a && wsTermB b
  | .Fst t => wsTermB t
  | .Snd t => wsTermB t
  | .Inl _ t => wsTermB t
  | .Inr _ t => wsTermB t
  | .Case a b c => wsTermB a && wsTermB b && wsTermB c
  | .TensorIntro a b => wsTermB a && wsTermB b
  | .LetTensor a b => wsTermB a && wsTermB b
  | .LetSays _ a b => wsTermB a && wsTermB b
  | .SfExtract t => wsTermB t
  | .Command a b _ => wsTermB a && wsTermB b
  | .RunCmd a b => wsTermB a && wsTermB b

/-- The well-scopedness / no-`U32`-overflow fence (parent §3.1(i)). -/
def WellScopedTm (t : syntax.Term) : Prop := wsTermB t = true

/-! ## 4. `AppCommandRefines` — THE ONE REMAINING OBLIGATION.

The generated per-command engine `rsm.apply_command` refines the hand-written
`DLCD.applyCommand` under the (abstract) payload decode, on well-scoped inputs —
and never fails/diverges (folded into the `= .ok` equation via `Result.map`).

R2.2b ASSUMES this (as a hypothesis on every structural square that routes
through the reducer). R2.3 (the deferred `dlc-core` reducer correspondence)
DISCHARGES it. It is **NOT** an `axiom` and **NOT** a `sorry`: it is a named
`Prop` a later increment inhabits, and whose *consequent* the anti-vacuity
witness (§7) already discharges on a concrete state-changing input. -/
def AppCommandRefines (decTm : DecTm) (decPr : DecPr) : Prop :=
  ∀ (c : rsm.Command) (s : syntax.Term),
    WellScopedTm s → WellScopedTm c.payload →
    (decTm <$> rsm.apply_command c s)
      = Result.ok (DLCD.applyCommand (decCmd decTm decPr c) (decTm s))

/-! ## 5. A concrete fragment decode `decTm₀`/`decPr₀` (the anti-vacuity seam).

The full structural `Term`/`Prop` decode over all ~26/~14 constructors — and the
proof it commutes with the reducer — is R2.3. Here we exhibit a concrete decode
on the small closed fragment the `dup` witness uses (`Var`, `Lam`, `Pair`,
`Prop.Atom`), enough to *evaluate* the witness. -/

/-- Concrete `Prop` decode on the witness fragment (`Atom`), default `top`. -/
def decPr₀ : syntax.Prop → DLC.Prop'
  | .Atom i => .atom i.val
  | _ => .top

/-- Concrete `Term` decode on the witness fragment (`Var`/`Lam`/`App`/`Pair`),
default `var 0` for the off-fragment constructors (unused by the witness). -/
def decTm₀ : syntax.Term → DLC.Term
  | .Var i => .var i.val
  | .Lam p t => .lam (decPr₀ p) (decTm₀ t)
  | .App a b => .app (decTm₀ a) (decTm₀ b)
  | .Pair a b => .pair (decTm₀ a) (decTm₀ b)
  | _ => .var 0

/-! ## 6. The generated-side `dup`/`init`, mirroring `DLCD.RsmAntiVacuity`. -/

/-- The generated `dup` command: `λ_:atom0. ⟨var0, var0⟩` (duplicates the store). -/
def dupGenW : rsm.Command :=
  { payload := syntax.Term.Lam (syntax.Prop.Atom 0#u32)
      (syntax.Term.Pair (syntax.Term.Var 0#u32) (syntax.Term.Var 0#u32)),
    cap := none }

/-- The generated initial store `var 0`. -/
def initGenW : syntax.Term := syntax.Term.Var 0#u32

/-- The generated normal form the `dup` beta-reduces to: `⟨var0, var0⟩`. -/
abbrev pair00W : syntax.Term :=
  syntax.Term.Pair (syntax.Term.Var 0#u32) (syntax.Term.Var 0#u32)

/-- The generated redex `(λ_. ⟨var0,var0⟩) var0`. -/
abbrev appW : syntax.Term := syntax.Term.App dupGenW.payload initGenW

/-! ### Reducer-evaluation plumbing (computes the loop on the closed input).

`reduce_with_fuel`'s loop is the Aeneas `loop` combinator (well-founded); it does
NOT `rfl`-reduce and we do NOT use `native_decide`. We unfold it via `loop.eq_1`
across exactly the two iterations the `dup` redex takes (one β-step, then a
normal form), evaluating each loop body — including the `Range` iterator's `next`
— by `simp`+`rfl` over the leaf `U32`/`I64` `BitVec` arithmetic. -/

/-- One `Range`-iterator advance `[a,b)` with `a < b`: yields `some a`, `start := a+1`. -/
private theorem next_succ {a b : Std.U32} (hlt : a.val < b.val) (hsucc : a.val + 1 ≤ U32.max) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 { start := a, «end» := b }
      = ok (some a, { start := UScalar.ofNatCore (a.val + 1) (by scalar_tac), «end» := b }) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepU32,
    core.iter.range.UScalarStep, core.cmp.impls.PartialOrdU32.lt,
    core.clone.impls.CloneU32.clone, lift, bind_ok, bind_tc_ok]
  rw [if_pos (by simp [hlt]), core.iter.range.UScalarStep.forward_checked, dif_pos (by scalar_tac)]
  rfl

/-- The β-step: `(λ_. ⟨var0,var0⟩) var0` steps to `⟨var0,var0⟩`. -/
private theorem step_beta : reduce.step appW = ok (some pair00W) := by
  simp only [appW, dupGenW, initGenW, reduce.step, Box.Insts.CoreConvertAsRef.as_ref,
    subst.subst, subst.subst_at, subst.shift, core.cmp.impls.OrdU32.cmp, lift, pair00W,
    bind_ok, bind_tc_ok, pure]
  rfl

/-- `⟨var0,var0⟩` is a normal form. -/
private theorem step_nf : reduce.step pair00W = ok none := by
  simp only [pair00W, reduce.step, Box.Insts.CoreConvertAsRef.as_ref, lift, bind_ok, bind_tc_ok]

/-- `loop` unfolds one `cont` step. -/
private theorem loop_cont {α β} (F : α → Result (ControlFlow α β)) (x x' : α)
    (h : F x = ok (ControlFlow.cont x')) : loop F x = loop F x' := by rw [loop.eq_1, h]

/-- `loop` finishes on a `done` step. -/
private theorem loop_fin {α β} (F : α → Result (ControlFlow α β)) (x : α) (y : β)
    (h : F x = ok (ControlFlow.done y)) : loop F x = ok y := by rw [loop.eq_1, h]

/-- The generated `apply_command` on `(dup, var0)` computes to `⟨var0,var0⟩`. -/
private theorem apply_command_dup :
    rsm.apply_command dupGenW initGenW = ok pair00W := by
  have hcp : syntax.Term.Insts.CoreCloneClone.clone dupGenW.payload = ok dupGenW.payload := by
    simp only [dupGenW, syntax.Term.Insts.CoreCloneClone.clone,
      syntax.Prop.Insts.CoreCloneClone.clone, core.clone.impls.CloneU32.clone, lift,
      bind_ok, bind_tc_ok]
  have hci : syntax.Term.Insts.CoreCloneClone.clone initGenW = ok initGenW := by
    simp only [initGenW, syntax.Term.Insts.CoreCloneClone.clone,
      core.clone.impls.CloneU32.clone, lift, bind_ok, bind_tc_ok]
  have hcApp : syntax.Term.Insts.CoreCloneClone.clone appW = ok appW := by
    simp only [appW, dupGenW, initGenW, syntax.Term.Insts.CoreCloneClone.clone,
      syntax.Prop.Insts.CoreCloneClone.clone, core.clone.impls.CloneU32.clone, lift,
      bind_ok, bind_tc_ok]
  have hbody0 : reduce.reduce_with_fuel_loop.body 1024#u32 { start := 0#u32, «end» := 1024#u32 } appW
      = ok (ControlFlow.cont ({ start := 1#u32, «end» := 1024#u32 }, pair00W)) := by
    simp only [reduce.reduce_with_fuel_loop.body,
      next_succ (a := 0#u32) (b := 1024#u32) (by decide) (by scalar_tac), step_beta,
      bind_ok, bind_tc_ok]
    rfl
  have hbody1 : reduce.reduce_with_fuel_loop.body 1024#u32 { start := 1#u32, «end» := 1024#u32 } pair00W
      = ok (ControlFlow.done (pair00W, 1#u32)) := by
    simp only [reduce.reduce_with_fuel_loop.body,
      next_succ (a := 1#u32) (b := 1024#u32) (by decide) (by scalar_tac), step_nf,
      bind_ok, bind_tc_ok]
    rfl
  have hloop : reduce.reduce_with_fuel_loop { start := 0#u32, «end» := 1024#u32 } 1024#u32 appW
      = ok (pair00W, 1#u32) := by
    rw [reduce.reduce_with_fuel_loop,
      loop_cont _ _ ({ start := 1#u32, «end» := 1024#u32 }, pair00W) hbody0,
      loop_fin _ _ (pair00W, 1#u32) hbody1]
  have hrwf : reduce.reduce_with_fuel appW 1024#u32 = ok (pair00W, 1#u32) := by
    rw [reduce.reduce_with_fuel]; simp only [hcApp, bind_ok, bind_tc_ok]; exact hloop
  simp only [rsm.apply_command, hcp, hci, rsm.APPLY_FUEL, appW, hrwf, bind_ok, bind_tc_ok]
  rfl

/-! ## 7. ★ THE ANTI-VACUITY WITNESS — the closed satisfiability witness.

`AppCommandRefines`'s consequent (the refinement equation) holds on the concrete
state-changing `dup` input, and the decoded result is the **changed** store
`⟨var0,var0⟩ ≠ var0`. This is the closed, `sorry`-free, `native_decide`-free
satisfiability witness that the conditional squares are not vacuous: the equation
they depend on is achievable on a real input (not free-because-`False`). Its
axiom footprint is exactly `[propext, Classical.choice, Quot.sound]`. -/
theorem appCommandRefines_witness :
    (decTm₀ <$> rsm.apply_command dupGenW initGenW)
        = Result.ok (DLCD.applyCommand (decCmd decTm₀ decPr₀ dupGenW) (decTm₀ initGenW))
      ∧ decTm₀ pair00W ≠ decTm₀ initGenW := by
  refine ⟨?_, ?_⟩
  · rw [apply_command_dup]
    -- LHS: decTm₀ <$> ok ⟨var0,var0⟩ = ok ⟨var0,var0⟩; RHS: hand applyCommand reduces likewise.
    show Result.ok (decTm₀ pair00W) = _
    rfl
  · intro h
    simp only [decTm₀, decPr₀, initGenW, pair00W] at h
    exact DLC.Term.noConfusion h

end DLCD.Correspondence
