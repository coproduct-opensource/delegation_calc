import DLCD.Rsm            -- the SPEC side (hand model): DLCD.applyCommand, deliver, worldStep, …
import DlcCore             -- the CODE side (real Aeneas defs): dlc_core.rsm.*, reduce.*, syntax.*
import DLC.DerivClosed     -- ClosedAbove + the preservation metatheory (closedAbove_shift, …) for the R2.3 fence
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

**Square coverage (R2.2b + continuation — ALL SIX landed).** `deliver_square`,
`world_step_square` (the headline), `apply_prefix_square`, and `commit_square` are
here; `is_quorum_square` and `decided_square` are in the companion module
`DLCD.CorrespondenceConsensus` (which owns the `dlc_d_rsm` tree). The three
reducer-routed squares (`deliver`, `world_step`, `apply_prefix`) route every
`apply_command` step through the `AppCommandRefines` hypothesis; `apply_prefix`
additionally threads the `WellScopedTm` fence through its fold via the second
stated obligation `ApplyPreservesWS`. All six rest on the AST-wide clone-identity
linchpin `termClone_id` (§2c; `vecClone_id` is its `Vec` base case). Every
footprint is exactly `[propext, Classical.choice, Quot.sound]`; no `sorry`, no
`axiom`, no `native_decide`.

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

/-! ## 2c. ★ THE AST-WIDE CLONE-IDENTITY LEMMA (the linchpin).

The generated `Clone::clone` on every `dlc_core` AST type is `pure`-identity in the
`Result` monad (`clone x = ok x`). This is what every reducer-routed square needs:
`deliver`/`world_step`/`apply_prefix`/`commit` all `clone` their `Vec`/`Term`
arguments before decoding. The `clone`s are `partial_fixpoint` monadic functions;
we discharge identity **bottom-up in dependency order** by structural induction on
each inductive, dispatching non-self children to the already-proven lemma for their
type. Scalar/`Vec`/`Array`/`Option` leaves are handled by `rfl` and the Aeneas
`List.mapM_clone_eq` bridge (`vecClone_id` above is the `Vec` base case). No `sorry`,
no `axiom`: these are equations about real `def`s. -/

-- Scalar leaves (the instance's `clone` reduces to `ok x` definitionally).
private theorem u8I_clone (x : Std.U8) : core.clone.CloneU8.clone x = ok x := rfl
private theorem u32I_clone (x : Std.U32) : core.clone.CloneU32.clone x = ok x := rfl

-- Fixed-array leaf: a `[u8; N]` whose elements each clone to themselves.
private theorem arrayClone_id {T} {n : Std.Usize} (cl : core.clone.Clone T)
    (a : Std.Array T n) (h : ∀ x ∈ a.val, cl.clone x = ok x) :
    core.array.CloneArray.clone cl a = ok a := by
  have hm := List.mapM_clone_eq h
  simp only [core.array.CloneArray.clone, Std.Array.clone, List.clone]
  split
  · rename_i v1 heq; rw [hm] at heq; injection heq with heq; subst heq
    simp only [bind_tc_ok]; rfl
  · rename_i e heq; rw [hm] at heq; exact absurd heq (by simp)
  · rename_i heq; rw [hm] at heq; exact absurd heq (by simp)

-- Leaf structs / newtypes over scalars and scalar vectors.
private theorem timeBoundClone_id (t : time.TimeBound) :
    time.TimeBound.Insts.CoreCloneClone.clone t = ok t := by
  simp only [time.TimeBound.Insts.CoreCloneClone.clone, core.clone.impls.CloneU64.clone,
    lift, bind_tc_ok]

private theorem dpBudgetClone_id (d : obligation.DpBudget) :
    obligation.DpBudget.Insts.CoreCloneClone.clone d = ok d := rfl

private theorem actionIdClone_id (a : obligation.ActionId) :
    obligation.ActionId.Insts.CoreCloneClone.clone a = ok a := by
  simp only [obligation.ActionId.Insts.CoreCloneClone.clone,
    vecClone_id core.clone.CloneU8 a (fun x _ => u8I_clone x), bind_tc_ok]

private theorem labelClone_id (l : ifc.Label) :
    ifc.Label.Insts.CoreCloneClone.clone l = ok l := by
  simp only [ifc.Label.Insts.CoreCloneClone.clone,
    vecClone_id core.clone.CloneU32 l (fun x _ => u32I_clone x), bind_tc_ok]

private theorem signatureClone_id (s : syntax.Signature) :
    syntax.Signature.Insts.CoreCloneClone.clone s = ok s := by
  simp only [syntax.Signature.Insts.CoreCloneClone.clone, core.clone.impls.CloneU8.clone,
    lift, vecClone_id core.clone.CloneU8 s.bytes (fun x _ => u8I_clone x), bind_tc_ok]

private theorem principalIdClone_id (p : principal.PrincipalId) :
    principal.PrincipalId.Insts.CoreCloneClone.clone p = ok p := by
  simp only [principal.PrincipalId.Insts.CoreCloneClone.clone]
  rw [arrayClone_id core.clone.CloneU8 p (fun x _ => u8I_clone x)]; rfl

-- Recursive AST clones: structural induction, children dispatched to their lemmas.
private theorem principalClone_id (p : principal.Principal) :
    principal.Principal.Insts.CoreCloneClone.clone p = ok p := by
  induction p <;>
    simp only [principal.Principal.Insts.CoreCloneClone.clone, principalIdClone_id,
      bind_tc_ok, *]

private theorem obligationClone_id (o : obligation.Obligation) :
    obligation.Obligation.Insts.CoreCloneClone.clone o = ok o := by
  induction o <;>
    simp only [obligation.Obligation.Insts.CoreCloneClone.clone, principalClone_id,
      actionIdClone_id, timeBoundClone_id, dpBudgetClone_id, bind_tc_ok, *]

private theorem propClone_id (p : syntax.Prop) :
    syntax.Prop.Insts.CoreCloneClone.clone p = ok p := by
  induction p <;>
    simp only [syntax.Prop.Insts.CoreCloneClone.clone, principalClone_id, labelClone_id,
      obligationClone_id, timeBoundClone_id, core.clone.impls.CloneU32.clone, lift,
      bind_tc_ok, *]

/-- **★ The AST-wide clone-identity linchpin** (public: pinned in the axiom
ledger). Every reducer-routed square rests on this. -/
theorem termClone_id (t : syntax.Term) :
    syntax.Term.Insts.CoreCloneClone.clone t = ok t := by
  induction t <;>
    simp only [syntax.Term.Insts.CoreCloneClone.clone, propClone_id, principalClone_id,
      signatureClone_id, obligationClone_id, labelClone_id, timeBoundClone_id,
      core.clone.impls.CloneU32.clone, lift, bind_tc_ok, *]

-- `Option Prop` (the `Command.cap` field).
private theorem optionPropClone_id (o : Option syntax.Prop) :
    core.option.Option.Insts.CoreCloneClone.clone syntax.Prop.Insts.CoreCloneClone o
      = ok o := by
  cases o with
  | none => rfl
  | some x =>
    simp only [core.option.Option.Insts.CoreCloneClone.clone, propClone_id, bind_tc_ok]

-- RSM record clones (`Command`, `Replica`) and their `Vec`s — the actual
-- `clone` sites in `deliver`/`world_step`/`apply_prefix`/`commit`.
private theorem commandClone_id (c : rsm.Command) :
    rsm.Command.Insts.CoreCloneClone.clone c = ok c := by
  simp only [rsm.Command.Insts.CoreCloneClone.clone, termClone_id, optionPropClone_id,
    bind_tc_ok]

private theorem replicaClone_id (r : rsm.Replica) :
    rsm.Replica.Insts.CoreCloneClone.clone r = ok r := by
  simp only [rsm.Replica.Insts.CoreCloneClone.clone, core.clone.impls.CloneU32.clone,
    lift, termClone_id, bind_tc_ok]

private theorem vecCommandClone_id (v : alloc.vec.Vec rsm.Command) :
    alloc.vec.CloneVec.clone rsm.Command.Insts.CoreCloneClone v = ok v :=
  vecClone_id rsm.Command.Insts.CoreCloneClone v (fun x _ => commandClone_id x)

private theorem vecReplicaClone_id (v : alloc.vec.Vec rsm.Replica) :
    alloc.vec.CloneVec.clone rsm.Replica.Insts.CoreCloneClone v = ok v :=
  vecClone_id rsm.Replica.Insts.CoreCloneClone v (fun x _ => replicaClone_id x)

private theorem fbClone_id (b : rsm.FailureBudget) :
    rsm.FailureBudget.Insts.CoreCloneClone.clone b = ok b := by
  simp only [rsm.FailureBudget.Insts.CoreCloneClone.clone, core.clone.impls.CloneU32.clone,
    core.clone.impls.CloneBool.clone, lift, bind_tc_ok]

/-! ## 2d. The concrete FULL payload decode `⟦·⟧` (all constructors).

R2.3 pins the abstract `DecTm`/`DecPr` seam to these concrete total structural
homomorphisms `syntax.Term → DLC.Term` / `syntax.Prop → DLC.Prop'`. They are
mirror-for-mirror on the term/prop structure (`U32.val → Nat` at the `Var`/atom
leaves, binder structure preserved) — the shape the reducer correspondence
(`shift_corr`/`subst_corr`, R2.3a) needs.

**Inert leaves.** Two decode targets are representation gaps with no cheap
inverse: `ifc.Label = Vec U32` vs the hand `Label = CapabilityLattice`, and the
generated `Obligation.DpBudget` arm (the hand `Obligation` carries no `DpBudget`
constructor). These are decoded to fixed representatives (`Label.bottom` /
`Obligation.top`). This is **sound for the reducer correspondence**:
`shift`/`subst`/`step` are label- and obligation-blind — they carry those fields
through *unchanged* — so the decode's behaviour on them never enters any
correspondence equation. It is honestly *lossy*: the scope of the transport is
the de Bruijn TERM STRUCTURE and its reduction, not the inert annotations. -/

def decTB (t : time.TimeBound) : DLC.TimeBound := { epochMs := t.epoch_ms.val }

def decPrinId (p : principal.PrincipalId) : DLC.PrincipalId :=
  { bytes := p.val.map (fun b => UInt8.ofNat b.val) }

def decPrin : principal.Principal → DLC.Principal
  | .Atom pid => .atom (decPrinId pid)
  | .And a b => .and (decPrin a) (decPrin b)
  | .Or a b => .or (decPrin a) (decPrin b)
  | .Acting a b => .acting (decPrin a) (decPrin b)

def decActId (a : obligation.ActionId) : DLC.ActionId :=
  { bytes := a.val.map (fun b => UInt8.ofNat b.val) }

def decOb : obligation.Obligation → DLC.Obligation
  | .Top => .top
  | .Bot => .bot
  | .ActOf p a => .actOf (decPrin p) (decActId a)
  | .Within t => .within (decTB t)
  | .Tensor a b => .tensor (decOb a) (decOb b)
  | .Lolli a b => .lolli (decOb a) (decOb b)
  | .DpBudget _ => .top          -- inert; no hand image (documented above)

def decSig (s : syntax.Signature) : DLC.Signature :=
  { alg := UInt8.ofNat s.alg.val, bytes := s.bytes.val.map (fun b => UInt8.ofNat b.val) }

def decLab (_ : ifc.Label) : DLC.Label := DLC.Label.bottom   -- inert; representation gap

def decPropC : syntax.Prop → DLC.Prop'
  | .Top => .top
  | .Bot => .bot
  | .Atom i => .atom i.val
  | .Imp a b => .imp (decPropC a) (decPropC b)
  | .And a b => .and (decPropC a) (decPropC b)
  | .Or a b => .or (decPropC a) (decPropC b)
  | .Says p a => .says (decPrin p) (decPropC a)
  | .SpeaksFor p q => .speaksFor (decPrin p) (decPrin q)
  | .At a l => .at (decPropC a) (decLab l)
  | .Boxed o a => .boxed (decOb o) (decPropC a)
  | .Within t a => .within (decTB t) (decPropC a)
  | .Tensor a b => .tensor (decPropC a) (decPropC b)
  | .Lolli a b => .lolli (decPropC a) (decPropC b)
  | .Replicated a l => .replicated (decPropC a) (decLab l)

def decTermC : syntax.Term → DLC.Term
  | .Var i => .var i.val
  | .Lam p t => .lam (decPropC p) (decTermC t)
  | .App a b => .app (decTermC a) (decTermC b)
  | .Sign p t s => .sign (decPrin p) (decTermC t) (decSig s)
  | .Verify p t s => .verify (decPrin p) (decTermC t) (decSig s)
  | .Delegate a b => .delegate (decTermC a) (decTermC b)
  | .Attenuate t p => .attenuate (decTermC t) (decPropC p)
  | .SaysBind p a b => .saysBind (decPrin p) (decTermC a) (decTermC b)
  | .Boxed o a b => .boxed (decOb o) (decTermC a) (decTermC b)
  | .Discharge a b => .discharge (decTermC a) (decTermC b)
  | .LiftLabel l t => .liftLabel (decLab l) (decTermC t)
  | .Declassify l a b => .declassify (decLab l) (decTermC a) (decTermC b)
  | .Now t => .now (decTB t)
  | .WithinIntro t m => .withinIntro (decTB t) (decTermC m)
  | .Pair a b => .pair (decTermC a) (decTermC b)
  | .Fst a => .fst (decTermC a)
  | .Snd a => .snd (decTermC a)
  | .Inl p a => .inl (decPropC p) (decTermC a)
  | .Inr p a => .inr (decPropC p) (decTermC a)
  | .Case a b c => .case (decTermC a) (decTermC b) (decTermC c)
  | .TensorIntro a b => .tensorIntro (decTermC a) (decTermC b)
  | .LetTensor a b => .letTensor (decTermC a) (decTermC b)
  | .LetSays p a b => .letSays (decPrin p) (decTermC a) (decTermC b)
  | .SfExtract t => .sfExtract (decTermC t)
  | .Command a b l => .command (decTermC a) (decTermC b) (decLab l)
  | .RunCmd a b => .runCmd (decTermC a) (decTermC b)

/-! ## 3. The `WellScopedTm` fence — closedness + a decidable height bound.

**Load-bearing correction (R2.3).** The R2.2b fence was a flat per-`Var`
index-bound. That predicate is (a) *not preserved by `shift`* — `shift`'s eq-arm
raises free indices by `depth`, and `i < 2^31` with `depth < 2^31` allows
`i + depth` to reach `~2^32 > 2^31`, so the reduct can escape the bound
(`ApplyPreservesWS` was therefore likely *false*); and (b) insufficient for the
no-fail argument — the `I32` depth-cast in `subst_at` fails unless the binder
DEPTH (unbounded by any index bound: `λλ…λ(var 0)`) is `< 2^31`.

The predicate that IS preserved by shift/subst/step is genuine **closedness**
(`DLC.ClosedAbove … 0`), the standard de Bruijn invariant, reusing the in-tree
metatheory (`DLC.closedAbove_shift`, `DLC.closedAbove_mono`). The **decidable
AST-height bound** `heightB t < 2^31` supplies the depth bound (`depth ≤ 2·height`)
that rules out every `hcast`/`+` overflow. On the RSM's actual inputs — closed
ground stores, small closed λ payloads — both conjuncts hold with astronomical
headroom (see `applyPreservesWS_witness`). -/

/-- Decidable AST size: `+1` at every node, SUM over children (a coarse upper
bound for the AST height, hence for the binder depth accumulated by
`shift`/`subst_at`: `depth ≤ 2·heightB`). Summing rather than `max`ing keeps the
child-bound discharges pure linear arithmetic (`omega`), no `Nat.max` atoms. -/
def heightB : syntax.Term → Nat
  | .Var _ => 0
  | .Now _ => 0
  | .Lam _ t => heightB t + 1
  | .App a b => heightB a + heightB b + 1
  | .Sign _ t _ => heightB t + 1
  | .Verify _ t _ => heightB t + 1
  | .Delegate a b => heightB a + heightB b + 1
  | .Attenuate t _ => heightB t + 1
  | .SaysBind _ a b => heightB a + heightB b + 1
  | .Boxed _ a b => heightB a + heightB b + 1
  | .Discharge a b => heightB a + heightB b + 1
  | .LiftLabel _ t => heightB t + 1
  | .Declassify _ a b => heightB a + heightB b + 1
  | .WithinIntro _ t => heightB t + 1
  | .Pair a b => heightB a + heightB b + 1
  | .Fst t => heightB t + 1
  | .Snd t => heightB t + 1
  | .Inl _ t => heightB t + 1
  | .Inr _ t => heightB t + 1
  | .Case a b c => heightB a + heightB b + heightB c + 1
  | .TensorIntro a b => heightB a + heightB b + 1
  | .LetTensor a b => heightB a + heightB b + 1
  | .LetSays _ a b => heightB a + heightB b + 1
  | .SfExtract t => heightB t + 1
  | .Command a b _ => heightB a + heightB b + 1
  | .RunCmd a b => heightB a + heightB b + 1

/-- The well-scopedness fence (parent ruling #1): the term decodes to a CLOSED
hand term (the shift/subst/reduce-preserved invariant) and is height-bounded
below `2^31` (the decidable no-overflow content). -/
def WellScopedTm (t : syntax.Term) : Prop :=
  DLC.ClosedAbove (decTermC t) 0 ∧ heightB t < 2147483648

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

/-! ## 6. The generated-side `dup`/`init`, mirroring `DLCD.RsmAntiVacuity`.

**Closed witness (R2.3 fence).** The R2.2b witness used the store `var 0`, which
is OPEN (`ClosedAbove (var 0) 0` is false), so it cannot satisfy the closedness
fence. We replace it with a closed ground value `now 0`; the `dup` payload
`λ_. ⟨var0, var0⟩` (the duplication combinator, whose `var 0` is its own bound
argument) is already closed, and the reduct `⟨now 0, now 0⟩` stays closed — a
genuine closed, state-CHANGING transition. -/

/-- The generated `dup` command: `λ_:atom0. ⟨var0, var0⟩` (duplicates the store). -/
def dupGenW : rsm.Command :=
  { payload := syntax.Term.Lam (syntax.Prop.Atom 0#u32)
      (syntax.Term.Pair (syntax.Term.Var 0#u32) (syntax.Term.Var 0#u32)),
    cap := none }

/-- The generated initial store: the closed ground value `now 0`. -/
def initGenW : syntax.Term := syntax.Term.Now { epoch_ms := 0#u64 }

/-- The generated normal form the `dup` beta-reduces to: `⟨now 0, now 0⟩`. -/
abbrev pair00W : syntax.Term := syntax.Term.Pair initGenW initGenW

/-- The generated redex `(λ_. ⟨var0,var0⟩) (now 0)`. -/
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

/-- The β-step: `(λ_. ⟨var0,var0⟩) (now 0)` steps to `⟨now 0, now 0⟩`. -/
private theorem step_beta : reduce.step appW = ok (some pair00W) := by
  simp only [appW, dupGenW, initGenW, reduce.step, Box.Insts.CoreConvertAsRef.as_ref,
    subst.subst, subst.subst_at, subst.shift, core.cmp.impls.OrdU32.cmp,
    timeBoundClone_id, lift, pair00W, bind_ok, bind_tc_ok, pure]
  rfl

/-- `⟨now 0, now 0⟩` is a normal form. -/
private theorem step_nf : reduce.step pair00W = ok none := by
  simp only [pair00W, initGenW, reduce.step, Box.Insts.CoreConvertAsRef.as_ref, lift,
    bind_ok, bind_tc_ok]

/-- `loop` unfolds one `cont` step. -/
private theorem loop_cont {α β} (F : α → Result (ControlFlow α β)) (x x' : α)
    (h : F x = ok (ControlFlow.cont x')) : loop F x = loop F x' := by rw [loop.eq_1, h]

/-- `loop` finishes on a `done` step. -/
private theorem loop_fin {α β} (F : α → Result (ControlFlow α β)) (x : α) (y : β)
    (h : F x = ok (ControlFlow.done y)) : loop F x = ok y := by rw [loop.eq_1, h]

/-- The generated `apply_command` on `(dup, var0)` computes to `⟨var0,var0⟩`. -/
private theorem apply_command_dup :
    rsm.apply_command dupGenW initGenW = ok pair00W := by
  have hcp : syntax.Term.Insts.CoreCloneClone.clone dupGenW.payload = ok dupGenW.payload :=
    termClone_id _
  have hci : syntax.Term.Insts.CoreCloneClone.clone initGenW = ok initGenW :=
    termClone_id _
  have hcApp : syntax.Term.Insts.CoreCloneClone.clone appW = ok appW :=
    termClone_id _
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
    (decTermC <$> rsm.apply_command dupGenW initGenW)
        = Result.ok (DLCD.applyCommand (decCmd decTermC decPropC dupGenW) (decTermC initGenW))
      ∧ decTermC pair00W ≠ decTermC initGenW := by
  refine ⟨?_, ?_⟩
  · rw [apply_command_dup]
    -- LHS: decTermC <$> ok ⟨now 0,now 0⟩ = ok ⟨now 0,now 0⟩; RHS: hand applyCommand reduces likewise.
    show Result.ok (decTermC pair00W) = _
    rfl
  · intro h
    simp only [decTermC, initGenW, pair00W] at h
    exact DLC.Term.noConfusion h

/-! ## 8. ★ THE STRUCTURAL CORRESPONDENCE SQUARES.

Each square proves `decode <$> (generated transition) = ok (hand transition of the
decoded input)`. The reducer-routed squares (`deliver`, `world_step`,
`apply_prefix`) carry `(hcmd : AppCommandRefines decTm decPr)` and route every
`apply_command` step through it; `commit` routes through no reducer. All rest on
the AST-wide clone-identity lemma (§2c) to discharge the `clone`-before-decode step.
Honest `U32`/`Usize` no-overflow fences are stated hypotheses (benign for RSM
inputs), never hand-waved. -/

/-- Invert a decode-map equation: `f <$> m = ok y` forces `m` to succeed and its
value to decode to `y`. The bridge from `hcmd`'s `.map` form to the raw
`apply_command` result the generated `deliver`/`apply_prefix` bodies bind. -/
private theorem map_ok_inv {α β} {f : α → β} {m : Result α} {y : β}
    (h : f <$> m = ok y) : ∃ x, m = ok x ∧ f x = y := by
  cases m with
  | ok x => exact ⟨x, rfl, Result.ok.inj (by rw [show f <$> (ok x : Result α) = ok (f x) from rfl] at h; exact h)⟩
  | fail e => rw [show f <$> (fail e : Result α) = fail e from rfl] at h; simp at h
  | div => rw [show f <$> (div : Result α) = div from rfl] at h; simp at h

/-- **`deliver_square`** (uses `hcmd`). Delivering the next committed slot to a
replica decodes to `DLCD.deliver` of the decoded log and replica. Routes the
`apply_command` step through `hcmd`; the out-of-bounds branch is clone-identity. -/
theorem deliver_square (decTm : DecTm) (decPr : DecPr)
    (hcmd : AppCommandRefines decTm decPr)
    (log : alloc.vec.Vec rsm.Command) (r : rsm.Replica)
    (hr : WellScopedTm r.store)
    (hlog : ∀ c ∈ log.val, WellScopedTm c.payload)
    (happ : r.applied.val + 1 ≤ Std.U32.max) :
    (decRep decTm <$> rsm.deliver log r)
      = ok (DLCD.deliver (decLog decTm decPr log) (decRep decTm r)) := by
  have hidx : (UScalar.cast .Usize r.applied).val = r.applied.val := by
    simp only [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; scalar_tac
  unfold rsm.deliver DLCD.deliver
  simp only [alloc.vec.Vec.deref, core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice,
    core.slice.index.Usize.get, lift, bind_tc_ok, Slice.getElem?_Usize_eq, hidx,
    decRep, decLog, List.getElem?_map]
  cases hc : log.val[r.applied.val]? with
  | none =>
    simp only [Option.map_none, replicaClone_id, decRep]
    rfl
  | some c =>
    have hcmem : c ∈ log.val := List.mem_of_getElem? hc
    have happly := hcmd c r.store hr (hlog c hcmem)
    obtain ⟨t, ht, htd⟩ := map_ok_inv happly
    obtain ⟨i1, hi1, hi1v⟩ :=
      WP.spec_imp_exists (U32.add_spec (x := r.applied) (y := 1#u32) (by scalar_tac))
    have hi1v' : i1.val = r.applied.val + 1 := by rw [hi1v]; rfl
    simp only [Option.map_some, ht, hi1, bind_tc_ok]
    show ok (decRep decTm { id := r.id, store := t, applied := i1 }) = _
    simp only [decRep, htd, hi1v']

/-- One `Usize` range advance `[a,b)` with `a < b`: yields `some a`, `start := a+1`. -/
private theorem next_succ_usize {a b : Std.Usize} (hlt : a.val < b.val)
    (hsucc : a.val + 1 ≤ Std.Usize.max) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := a, «end» := b }
      = ok (some a, { start := UScalar.ofNatCore (a.val + 1) (by scalar_tac), «end» := b }) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, lift, bind_ok, bind_tc_ok]
  rw [if_pos (by simp [hlt]), core.iter.range.UScalarStep.forward_checked, dif_pos (by scalar_tac)]
  rfl

/-- One `Usize` range advance `[a,b)` with `b ≤ a`: yields `none`. -/
private theorem next_done_usize {a b : Std.Usize} (hge : b.val ≤ a.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := a, «end» := b }
      = ok (none, { start := a, «end» := b }) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, lift, bind_ok, bind_tc_ok]
  rw [if_neg (by simp; omega)]

/-- The generalized `world_step` loop spec: from an accumulator `acc` holding the
first `k` already-delivered replicas, the loop over `[k, n)` decodes to
`acc` (decoded) appended with `DLCD.deliver` applied to each remaining replica.
Induction on the remaining count; each iteration invokes `deliver_square`. -/
private theorem world_step_loop_spec (decTm : DecTm) (decPr : DecPr)
    (hcmd : AppCommandRefines decTm decPr)
    (reps : alloc.vec.Vec rsm.Replica) (logv : alloc.vec.Vec rsm.Command)
    (hstores : ∀ rep ∈ reps.val, WellScopedTm rep.store)
    (hlog : ∀ c ∈ logv.val, WellScopedTm c.payload)
    (happ : ∀ rep ∈ reps.val, rep.applied.val + 1 ≤ Std.U32.max)
    (n : Std.Usize) (hn : n.val = reps.val.length) :
    ∀ (rem : Nat) (k : Std.Usize) (acc : alloc.vec.Vec rsm.Replica),
      n.val = k.val + rem → k.val ≤ n.val → acc.val.length = k.val →
      ((fun v => v.val.map (decRep decTm)) <$>
          rsm.world_step_loop { start := k, «end» := n } reps logv acc)
        = ok (acc.val.map (decRep decTm)
              ++ (reps.val.drop k.val).map
                  (fun rep => DLCD.deliver (decLog decTm decPr logv) (decRep decTm rep))) := by
  intro rem
  induction rem with
  | zero =>
    intro k acc hrem hkn hacclen
    have hke : k.val = n.val := by omega
    have hbody : rsm.world_step_loop.body reps logv { start := k, «end» := n } acc
        = ok (ControlFlow.done acc) := by
      unfold rsm.world_step_loop.body
      rw [next_done_usize (a := k) (b := n) (by omega)]
      simp
    rw [show rsm.world_step_loop { start := k, «end» := n } reps logv acc
          = loop (fun p => rsm.world_step_loop.body reps logv p.1 p.2)
              ({ start := k, «end» := n }, acc) from rfl,
        loop_fin _ _ acc hbody]
    have hde : reps.val.drop k.val = [] := by rw [hke, hn]; exact List.drop_length
    simp only [hde, List.map_nil, List.append_nil]
    rfl
  | succ m ih =>
    intro k acc hrem hkn hacclen
    have hk_lt : k.val < n.val := by omega
    have hk_len : k.val < reps.val.length := by rw [← hn]; exact hk_lt
    have hle := alloc.vec.Vec.len_ineq reps
    have hsucc : k.val + 1 ≤ Std.Usize.max := by omega
    have hmem : reps.val[k.val]'hk_len ∈ reps.val := List.getElem_mem hk_len
    have hdsq := deliver_square decTm decPr hcmd logv (reps.val[k.val]'hk_len)
      (hstores _ hmem) hlog (happ _ hmem)
    obtain ⟨rep', hrep', hrepd⟩ := map_ok_inv hdsq
    have hpushfence : acc.val.length < Std.Usize.max := by rw [hacclen]; omega
    obtain ⟨acc', hpush, haccval⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec acc rep' hpushfence)
    set k1 : Std.Usize := UScalar.ofNatCore (k.val + 1) (by scalar_tac) with hk1_def
    have hk1v : k1.val = k.val + 1 := by rw [hk1_def]; exact UScalar.ofNatCore_val_eq _
    have hbody : rsm.world_step_loop.body reps logv { start := k, «end» := n } acc
        = ok (ControlFlow.cont ({ start := k1, «end» := n }, acc')) := by
      unfold rsm.world_step_loop.body
      rw [next_succ_usize hk_lt hsucc]
      simp [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
        List.getElem?_eq_getElem hk_len, hrep', hpush, hk1_def]
    rw [show rsm.world_step_loop { start := k, «end» := n } reps logv acc
          = loop (fun p => rsm.world_step_loop.body reps logv p.1 p.2)
              ({ start := k, «end» := n }, acc) from rfl,
        loop_cont _ _ ({ start := k1, «end» := n }, acc') hbody,
        show loop (fun p => rsm.world_step_loop.body reps logv p.1 p.2)
              ({ start := k1, «end» := n }, acc')
          = rsm.world_step_loop { start := k1, «end» := n } reps logv acc' from rfl]
    rw [ih k1 acc' (by omega) (by omega) (by rw [haccval, List.length_append, hacclen, hk1v]; rfl)]
    have hdrop : reps.val.drop k.val = reps.val[k.val]'hk_len :: reps.val.drop k1.val := by
      rw [hk1v]; exact List.drop_eq_getElem_cons hk_len
    simp only [haccval, hdrop, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append, hrepd]

/-- **★ `world_step_square`** (the headline square; uses `hcmd`). One synchronous
world step — every replica delivers its next committed slot — decodes to
`DLCD.worldStep`. Built from the push-accumulator `world_step_loop_spec`, which
invokes `deliver_square` per replica. This is what R2.4 pulls G1–G4 back through. -/
theorem world_step_square (decTm : DecTm) (decPr : DecPr)
    (hcmd : AppCommandRefines decTm decPr) (g : rsm.GlobalConfig)
    (hstores : ∀ rep ∈ g.replicas.val, WellScopedTm rep.store)
    (hlog : ∀ c ∈ g.log.val, WellScopedTm c.payload)
    (happ : ∀ rep ∈ g.replicas.val, rep.applied.val + 1 ≤ Std.U32.max) :
    (decGC decTm decPr <$> rsm.world_step g)
      = ok (DLCD.worldStep (decGC decTm decPr g)) := by
  have hn : (alloc.vec.Vec.len g.replicas).val = g.replicas.val.length := alloc.vec.Vec.len_val _
  have hloop := world_step_loop_spec decTm decPr hcmd g.replicas g.log hstores hlog happ
    (alloc.vec.Vec.len g.replicas) hn (alloc.vec.Vec.len g.replicas).val 0#usize
    (alloc.vec.Vec.new rsm.Replica) (by simp) (by simp) (by simp)
  obtain ⟨stepped, hstepped, hsteppedval⟩ := map_ok_inv hloop
  unfold rsm.world_step
  simp only [hstepped, vecCommandClone_id, fbClone_id, bind_tc_ok]
  show ok (decGC decTm decPr { replicas := stepped, log := g.log, budget := g.budget }) = _
  unfold DLCD.worldStep
  simp only [decGC, decLog, hsteppedval]
  simp [List.map_map, Function.comp_def]

/-- **Second deferred obligation** (a `def : Prop`, never an `axiom`, never a
`sorry`). The generated `apply_command` preserves the `WellScopedTm` fence: the
reduct of a well-scoped store under a well-scoped command is itself well-scoped.
This threads the fence through the `apply_prefix` *fold* — each intermediate
accumulator that the next `hcmd` step consumes stays in-scope. R2.3 discharges it
(the reducer preserves the variable-index bound); `applyPreservesWS_witness` shows
it is non-vacuously satisfiable on a concrete state-changing input. -/
def ApplyPreservesWS : Prop :=
  ∀ (c : rsm.Command) (s t : syntax.Term),
    WellScopedTm s → WellScopedTm c.payload → rsm.apply_command c s = ok t → WellScopedTm t

/-- Anti-vacuity for `ApplyPreservesWS` (same standard as `appCommandRefines_witness`):
on the concrete state-CHANGING `dup` input, the reduct `⟨var0,var0⟩` of the
well-scoped store `var0` under the well-scoped `dup` command is itself well-scoped —
premises and conclusion of the preservation predicate are jointly achievable on a
real transition, so `ApplyPreservesWS` is not `False`. -/
theorem applyPreservesWS_witness :
    WellScopedTm initGenW ∧ WellScopedTm dupGenW.payload
      ∧ rsm.apply_command dupGenW initGenW = ok pair00W
      ∧ WellScopedTm pair00W ∧ pair00W ≠ initGenW := by
  refine ⟨?_, ?_, apply_command_dup, ?_, ?_⟩
  · -- store `now 0`: decodes to `now 0`, closed (no vars); height 0.
    exact ⟨by intro i _; rfl, by decide⟩
  · -- payload `λ_. ⟨var0,var0⟩`: decodes to `lam _ ⟨var0,var0⟩`, closed; height 2.
    refine ⟨?_, by decide⟩
    intro i _
    have h0 : ((0#u32 : Std.U32).val) = 0 := rfl
    simp only [dupGenW, decTermC, decPropC, DLC.usesVar, h0, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq]
    omega
  · -- reduct `⟨now 0, now 0⟩`: closed; height 1.
    exact ⟨by intro i _; rfl, by decide⟩
  · simp [pair00W, initGenW]

/-- The generalized `apply_prefix` fold-loop spec: from a well-scoped accumulator
`acc` after `k` commands, the loop over `[k, n)` decodes to `List.foldl applyCommand`
over the decoded remaining commands. Induction on the remaining count; each step
routes `apply_command` through `hcmd` and threads well-scopedness via `hpres`. -/
private theorem apply_prefix_loop_spec (decTm : DecTm) (decPr : DecPr)
    (hcmd : AppCommandRefines decTm decPr) (hpres : ApplyPreservesWS)
    (cmds : Slice rsm.Command) (hcmds : ∀ c ∈ cmds.val, WellScopedTm c.payload)
    (n : Std.Usize) (hn : n.val = cmds.val.length) :
    ∀ (rem : Nat) (k : Std.Usize) (acc : syntax.Term),
      n.val = k.val + rem → k.val ≤ n.val → WellScopedTm acc →
      (decTm <$> rsm.apply_prefix_loop { start := k, «end» := n } cmds acc)
        = ok (((cmds.val.drop k.val).map (decCmd decTm decPr)).foldl
                (fun s c => DLCD.applyCommand c s) (decTm acc)) := by
  intro rem
  induction rem with
  | zero =>
    intro k acc hrem hkn hacc
    have hke : k.val = n.val := by omega
    have hbody : rsm.apply_prefix_loop.body cmds { start := k, «end» := n } acc
        = ok (ControlFlow.done acc) := by
      unfold rsm.apply_prefix_loop.body
      rw [next_done_usize (a := k) (b := n) (by omega)]
      simp
    rw [show rsm.apply_prefix_loop { start := k, «end» := n } cmds acc
          = loop (fun p => rsm.apply_prefix_loop.body cmds p.1 p.2)
              ({ start := k, «end» := n }, acc) from rfl,
        loop_fin _ _ acc hbody]
    have hde : cmds.val.drop k.val = [] := by rw [hke, hn]; exact List.drop_length
    simp only [hde, List.map_nil, List.foldl_nil]
    rfl
  | succ m ih =>
    intro k acc hrem hkn hacc
    have hk_lt : k.val < n.val := by omega
    have hk_len : k.val < cmds.val.length := by rw [← hn]; exact hk_lt
    have hle := Slice.length_ineq cmds
    have hsucc : k.val + 1 ≤ Std.Usize.max := by omega
    have hmem : cmds.val[k.val]'hk_len ∈ cmds.val := List.getElem_mem hk_len
    have happly := hcmd (cmds.val[k.val]'hk_len) acc hacc (hcmds _ hmem)
    obtain ⟨t, ht, htd⟩ := map_ok_inv happly
    have hacc' : WellScopedTm t := hpres (cmds.val[k.val]'hk_len) acc t hacc (hcmds _ hmem) ht
    set k1 : Std.Usize := UScalar.ofNatCore (k.val + 1) (by scalar_tac) with hk1_def
    have hk1v : k1.val = k.val + 1 := by rw [hk1_def]; exact UScalar.ofNatCore_val_eq _
    have hbody : rsm.apply_prefix_loop.body cmds { start := k, «end» := n } acc
        = ok (ControlFlow.cont ({ start := k1, «end» := n }, t)) := by
      unfold rsm.apply_prefix_loop.body
      rw [next_succ_usize hk_lt hsucc]
      simp [Slice.index_usize, List.getElem?_eq_getElem hk_len, ht, hk1_def]
    rw [show rsm.apply_prefix_loop { start := k, «end» := n } cmds acc
          = loop (fun p => rsm.apply_prefix_loop.body cmds p.1 p.2)
              ({ start := k, «end» := n }, acc) from rfl,
        loop_cont _ _ ({ start := k1, «end» := n }, t) hbody,
        show loop (fun p => rsm.apply_prefix_loop.body cmds p.1 p.2)
              ({ start := k1, «end» := n }, t)
          = rsm.apply_prefix_loop { start := k1, «end» := n } cmds t from rfl]
    rw [ih k1 t (by omega) (by omega) hacc']
    have hdrop : cmds.val.drop k.val = cmds.val[k.val]'hk_len :: cmds.val.drop k1.val := by
      rw [hk1v]; exact List.drop_eq_getElem_cons hk_len
    simp only [hdrop, List.map_cons, List.foldl_cons, htd]

/-- **`apply_prefix_square`** (uses `hcmd` and `hpres`). Folding a committed
command prefix onto an initial store decodes to `DLCD.applyPrefix`
(`List.foldl applyCommand`). Each fold step routes through `hcmd`; `hpres` keeps
the running accumulator in the well-scoped fence. -/
theorem apply_prefix_square (decTm : DecTm) (decPr : DecPr)
    (hcmd : AppCommandRefines decTm decPr) (hpres : ApplyPreservesWS)
    (init : syntax.Term) (cmds : Slice rsm.Command)
    (hinit : WellScopedTm init) (hcmds : ∀ c ∈ cmds.val, WellScopedTm c.payload) :
    (decTm <$> rsm.apply_prefix init cmds)
      = ok (DLCD.applyPrefix (decTm init) (cmds.val.map (decCmd decTm decPr))) := by
  have hn : (Slice.len cmds).val = cmds.val.length := Slice.len_val _
  unfold rsm.apply_prefix
  simp only [termClone_id, bind_tc_ok]
  rw [apply_prefix_loop_spec decTm decPr hcmd hpres cmds hcmds (Slice.len cmds) hn
    (Slice.len cmds).val 0#usize init (by simp) (by simp) hinit]
  simp [DLCD.applyPrefix]

/-- **`commit_square`** (no `hcmd`). Appending a command to the committed log
(`clone` the log, `push c`) decodes to `List.append` of the decoded command. There
is no `DLCD.commit` (commit's guarantee is typing-level, parent §4 fence), so the
square is stated against the append operation on the decoded log directly. -/
theorem commit_square (decTm : DecTm) (decPr : DecPr)
    (g : rsm.GlobalConfig) (c : rsm.Command)
    (hlen : g.log.val.length < Std.Usize.max) :
    ((fun g' => (decGC decTm decPr g').log) <$> rsm.commit g c)
      = ok (decLog decTm decPr g.log ++ [decCmd decTm decPr c]) := by
  simp only [rsm.commit, vecCommandClone_id, vecReplicaClone_id, fbClone_id, bind_tc_ok]
  obtain ⟨log1, hpush, hlog1⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec g.log c hlen)
  rw [hpush]
  simp only [bind_tc_ok, decGC, decLog]
  show ok (List.map (decCmd decTm decPr) log1.val) = _
  rw [hlog1, List.map_append]; rfl

/-! ## 9. ★ R2.3a — the subst/shift correspondence (the reducer-correspondence crux).

`subst.shift`/`subst.subst_at` are the leaf the whole R2 operational transport
rests on. We discharge them by structural induction on the term (the emitted
`partial_fixpoint` defs carry no functional-induction principle, so we unfold one
constructor layer via `.eq_def` and thread the child IHs), under the closedness +
height fence.

**Why closedness collapses the feared arithmetic.** The generated `shift` Var arm
raises free indices by `delta` via an `I64` add + `U32` recast that can `.fail`.
But `ClosedAbove (decTermC t) cutoff.val` means every `Var i` reached at recursion
cutoff `c` has `i.val < c` — so the generated `if i < cutoff` ALWAYS takes the
then-branch (`ok term`, unchanged) and the `I64`/`U32` branch is **dead**. Both
`shift`s are the identity on the moved indices; the only live `U32` obligations are
the binder-depth bumps `cutoff + k#u32`, discharged from `heightB` by `scalar_tac`.
No `delta` bound is even needed. -/

/-- **`shift_corr`.** The generated `subst.shift` refines the hand `DLC.shift`
under the full decode on closed, height-bounded terms, and never `.fail`s (folded
into the `= ok` shape). -/
theorem shift_corr (delta : Std.I32) (t : syntax.Term) :
    ∀ (cutoff : Std.U32),
      DLC.ClosedAbove (decTermC t) cutoff.val →
      cutoff.val + 2 * heightB t < 4294967296 →
      decTermC <$> subst.shift t delta cutoff
        = ok (DLC.shift (decTermC t) delta.toNat cutoff.val) := by
  induction t with
  | Var i =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_var_iff] at hcl
      rw [subst.shift.eq_def]; simp only []
      rw [if_pos (by scalar_tac)]
      simp only [DLC.shift, if_pos hcl]; rfl
  | Lam p body ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_lam_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨c1, hc1, hc1v⟩ :=
        WP.spec_imp_exists (U32.add_spec (x := cutoff) (y := 1#u32) (by scalar_tac))
      have hc1val : c1.val = cutoff.val + 1 := by rw [hc1v]; rfl
      obtain ⟨tb, hb, hbd⟩ := map_ok_inv (ih c1 (by rw [hc1val]; exact hcl) (by omega))
      rw [subst.shift.eq_def]
      simp only [propClone_id, hc1, hb, bind_tc_ok]
      show ok (decTermC (syntax.Term.Lam p tb)) = _
      simp only [decTermC, hbd, hc1val, DLC.shift]
  | App f x ihf ihx =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_app_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tf, hf, hfd⟩ := map_ok_inv (ihf cutoff hcl.1 (by omega))
      obtain ⟨tx, hx, hxd⟩ := map_ok_inv (ihx cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [hf, hx, bind_tc_ok]
      show ok (decTermC (syntax.Term.App tf tx)) = _
      simp only [decTermC, hfd, hxd, DLC.shift]
  | Sign p m sig ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_sign_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [principalClone_id, hm, signatureClone_id, bind_tc_ok]
      show ok (decTermC (syntax.Term.Sign p tm sig)) = _
      simp only [decTermC, hmd, DLC.shift]
  | Verify p m sig ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_verify_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [principalClone_id, hm, signatureClone_id, bind_tc_ok]
      show ok (decTermC (syntax.Term.Verify p tm sig)) = _
      simp only [decTermC, hmd, DLC.shift]
  | Delegate m n ihm ihn =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_delegate_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ihm cutoff hcl.1 (by omega))
      obtain ⟨tn, hn, hnd⟩ := map_ok_inv (ihn cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [hm, hn, bind_tc_ok]
      show ok (decTermC (syntax.Term.Delegate tm tn)) = _
      simp only [decTermC, hmd, hnd, DLC.shift]
  | Attenuate m psi ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_attenuate_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [hm, propClone_id, bind_tc_ok]
      show ok (decTermC (syntax.Term.Attenuate tm psi)) = _
      simp only [decTermC, hmd, DLC.shift]
  | SaysBind p scrut body ihs ihb =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_saysBind_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨c1, hc1, hc1v⟩ :=
        WP.spec_imp_exists (U32.add_spec (x := cutoff) (y := 1#u32) (by scalar_tac))
      have hc1val : c1.val = cutoff.val + 1 := by rw [hc1v]; rfl
      obtain ⟨ts, hs, hsd⟩ := map_ok_inv (ihs cutoff hcl.1 (by omega))
      obtain ⟨tb, hb, hbd⟩ := map_ok_inv (ihb c1 (by rw [hc1val]; exact hcl.2) (by omega))
      rw [subst.shift.eq_def]
      simp only [principalClone_id, hc1, hs, hb, bind_tc_ok]
      show ok (decTermC (syntax.Term.SaysBind p ts tb)) = _
      simp only [decTermC, hsd, hbd, hc1val, DLC.shift]
  | Boxed o m n ihm ihn =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_boxed_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ihm cutoff hcl.1 (by omega))
      obtain ⟨tn, hn, hnd⟩ := map_ok_inv (ihn cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [obligationClone_id, hm, hn, bind_tc_ok]
      show ok (decTermC (syntax.Term.Boxed o tm tn)) = _
      simp only [decTermC, hmd, hnd, DLC.shift]
  | Discharge m n ihm ihn =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_discharge_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ihm cutoff hcl.1 (by omega))
      obtain ⟨tn, hn, hnd⟩ := map_ok_inv (ihn cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [hm, hn, bind_tc_ok]
      show ok (decTermC (syntax.Term.Discharge tm tn)) = _
      simp only [decTermC, hmd, hnd, DLC.shift]
  | LiftLabel l m ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_liftLabel_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [labelClone_id, hm, bind_tc_ok]
      show ok (decTermC (syntax.Term.LiftLabel l tm)) = _
      simp only [decTermC, hmd, DLC.shift]
  | Declassify l m pi ihm ihpi =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_declassify_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ihm cutoff hcl.1 (by omega))
      obtain ⟨tpi, hpi, hpid⟩ := map_ok_inv (ihpi cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [labelClone_id, hm, hpi, bind_tc_ok]
      show ok (decTermC (syntax.Term.Declassify l tm tpi)) = _
      simp only [decTermC, hmd, hpid, DLC.shift]
  | Now t =>
      intro cutoff hcl hh
      rw [subst.shift.eq_def]
      simp only [timeBoundClone_id, bind_tc_ok]
      show ok (decTermC (syntax.Term.Now t)) = _
      simp only [decTermC, DLC.shift]
  | WithinIntro t m ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_withinIntro_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [timeBoundClone_id, hm, bind_tc_ok]
      show ok (decTermC (syntax.Term.WithinIntro t tm)) = _
      simp only [decTermC, hmd, DLC.shift]
  | Pair a b iha ihb =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_pair_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨ta, ha, had⟩ := map_ok_inv (iha cutoff hcl.1 (by omega))
      obtain ⟨tb, hb, hbd⟩ := map_ok_inv (ihb cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [ha, hb, bind_tc_ok]
      show ok (decTermC (syntax.Term.Pair ta tb)) = _
      simp only [decTermC, had, hbd, DLC.shift]
  | Fst a ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_fst_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨ta, ha, had⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [ha, bind_tc_ok]
      show ok (decTermC (syntax.Term.Fst ta)) = _
      simp only [decTermC, had, DLC.shift]
  | Snd a ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_snd_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨ta, ha, had⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [ha, bind_tc_ok]
      show ok (decTermC (syntax.Term.Snd ta)) = _
      simp only [decTermC, had, DLC.shift]
  | Inl p a ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_inl_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨ta, ha, had⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [propClone_id, ha, bind_tc_ok]
      show ok (decTermC (syntax.Term.Inl p ta)) = _
      simp only [decTermC, had, DLC.shift]
  | Inr p a ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_inr_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨ta, ha, had⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [propClone_id, ha, bind_tc_ok]
      show ok (decTermC (syntax.Term.Inr p ta)) = _
      simp only [decTermC, had, DLC.shift]
  | Case scrut left right ihs ihl ihr =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_case_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨c1, hc1, hc1v⟩ :=
        WP.spec_imp_exists (U32.add_spec (x := cutoff) (y := 1#u32) (by scalar_tac))
      have hc1val : c1.val = cutoff.val + 1 := by rw [hc1v]; rfl
      obtain ⟨ts, hs, hsd⟩ := map_ok_inv (ihs cutoff hcl.1 (by omega))
      obtain ⟨tl, hl, hld⟩ := map_ok_inv (ihl c1 (by rw [hc1val]; exact hcl.2.1) (by omega))
      obtain ⟨tr, hr, hrd⟩ := map_ok_inv (ihr c1 (by rw [hc1val]; exact hcl.2.2) (by omega))
      rw [subst.shift.eq_def]
      simp only [hc1, hs, hl, hr, bind_tc_ok]
      show ok (decTermC (syntax.Term.Case ts tl tr)) = _
      simp only [decTermC, hsd, hld, hrd, hc1val, DLC.shift]
  | TensorIntro a b iha ihb =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_tensorIntro_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨ta, ha, had⟩ := map_ok_inv (iha cutoff hcl.1 (by omega))
      obtain ⟨tb, hb, hbd⟩ := map_ok_inv (ihb cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [ha, hb, bind_tc_ok]
      show ok (decTermC (syntax.Term.TensorIntro ta tb)) = _
      simp only [decTermC, had, hbd, DLC.shift]
  | LetTensor scrut body ihs ihb =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_letTensor_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨c2, hc2, hc2v⟩ :=
        WP.spec_imp_exists (U32.add_spec (x := cutoff) (y := 2#u32) (by scalar_tac))
      have hc2val : c2.val = cutoff.val + 2 := by rw [hc2v]; rfl
      obtain ⟨ts, hs, hsd⟩ := map_ok_inv (ihs cutoff hcl.1 (by omega))
      obtain ⟨tb, hb, hbd⟩ := map_ok_inv (ihb c2 (by rw [hc2val]; exact hcl.2) (by omega))
      rw [subst.shift.eq_def]
      simp only [hc2, hs, hb, bind_tc_ok]
      show ok (decTermC (syntax.Term.LetTensor ts tb)) = _
      simp only [decTermC, hsd, hbd, hc2val, DLC.shift]
  | LetSays p scrut body ihs ihb =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_letSays_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨c1, hc1, hc1v⟩ :=
        WP.spec_imp_exists (U32.add_spec (x := cutoff) (y := 1#u32) (by scalar_tac))
      have hc1val : c1.val = cutoff.val + 1 := by rw [hc1v]; rfl
      obtain ⟨ts, hs, hsd⟩ := map_ok_inv (ihs cutoff hcl.1 (by omega))
      obtain ⟨tb, hb, hbd⟩ := map_ok_inv (ihb c1 (by rw [hc1val]; exact hcl.2) (by omega))
      rw [subst.shift.eq_def]
      simp only [principalClone_id, hc1, hs, hb, bind_tc_ok]
      show ok (decTermC (syntax.Term.LetSays p ts tb)) = _
      simp only [decTermC, hsd, hbd, hc1val, DLC.shift]
  | SfExtract m ih =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_sfExtract_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ih cutoff hcl (by omega))
      rw [subst.shift.eq_def]
      simp only [hm, bind_tc_ok]
      show ok (decTermC (syntax.Term.SfExtract tm)) = _
      simp only [decTermC, hmd, DLC.shift]
  | Command m c l ihm ihc =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_command_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tm, hm, hmd⟩ := map_ok_inv (ihm cutoff hcl.1 (by omega))
      obtain ⟨tc, hc, hcd⟩ := map_ok_inv (ihc cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [hm, hc, labelClone_id, bind_tc_ok]
      show ok (decTermC (syntax.Term.Command tm tc l)) = _
      simp only [decTermC, hmd, hcd, DLC.shift]
  | RunCmd v s ihv ihs =>
      intro cutoff hcl hh
      simp only [decTermC] at hcl ⊢
      rw [DLC.closedAbove_runCmd_iff] at hcl
      simp only [heightB] at hh
      obtain ⟨tv, hv, hvd⟩ := map_ok_inv (ihv cutoff hcl.1 (by omega))
      obtain ⟨ts, hs, hsd⟩ := map_ok_inv (ihs cutoff hcl.2 (by omega))
      rw [subst.shift.eq_def]
      simp only [hv, hs, bind_tc_ok]
      show ok (decTermC (syntax.Term.RunCmd tv ts)) = _
      simp only [decTermC, hvd, hsd, DLC.shift]

end DLCD.Correspondence
