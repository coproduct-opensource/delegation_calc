import DlcCore

/-!
# AST-wide clone-identity for the Aeneas `dlc_core` types

The generated `Clone::clone` on every `dlc_core` AST type is `pure`-identity in the `Result`
monad (`clone x = ok x`). Extracted here (public, `DlcCore`-only — no RSM/DLCD coupling) because
BOTH the reducer-routed squares (`lean/DLCD/Correspondence.lean`) and the `infer_square` checker
transport (`lean/DLC/DecideSquare.lean`) need it: `decide.infer` clones `phi`/`ctx` on its `Var`
and `Lam` arms, and every structural arm rebuilds through a cloned child. Discharged bottom-up in
dependency order by structural induction; scalar/`Vec`/`Array` leaves via `rfl` and the Aeneas
`List.mapM_clone_eq` bridge. No `sorry`, no `axiom` — equations about real `def`s.
-/

namespace DLC.CloneId

open Aeneas Aeneas.Std Result
open dlc_core

/-- A `Vec` whose elements each clone to themselves clones to itself. -/
theorem vecClone_id {T} (cl : core.clone.Clone T) (v : alloc.vec.Vec T)
    (h : ∀ x ∈ v.val, cl.clone x = ok x) :
    alloc.vec.CloneVec.clone cl v = ok v := by
  have hm := List.mapM_clone_eq h
  simp only [alloc.vec.CloneVec.clone, Slice.clone, List.clone]
  split
  · rename_i v1 heq; rw [hm] at heq; injection heq with heq; subst heq
    simp only [bind_tc_ok]; rfl
  · rename_i e heq; rw [hm] at heq; exact absurd heq (by simp)
  · rename_i heq; rw [hm] at heq; exact absurd heq (by simp)

theorem u8I_clone (x : Std.U8) : core.clone.CloneU8.clone x = ok x := rfl
theorem u32I_clone (x : Std.U32) : core.clone.CloneU32.clone x = ok x := rfl

/-- A fixed `[T; N]` array whose elements each clone to themselves. -/
theorem arrayClone_id {T} {n : Std.Usize} (cl : core.clone.Clone T)
    (a : Std.Array T n) (h : ∀ x ∈ a.val, cl.clone x = ok x) :
    core.array.CloneArray.clone cl a = ok a := by
  have hm := List.mapM_clone_eq h
  simp only [core.array.CloneArray.clone, Std.Array.clone, List.clone]
  split
  · rename_i v1 heq; rw [hm] at heq; injection heq with heq; subst heq
    simp only [bind_tc_ok]; rfl
  · rename_i e heq; rw [hm] at heq; exact absurd heq (by simp)
  · rename_i heq; rw [hm] at heq; exact absurd heq (by simp)

theorem timeBoundClone_id (t : time.TimeBound) :
    time.TimeBound.Insts.CoreCloneClone.clone t = ok t := by
  simp only [time.TimeBound.Insts.CoreCloneClone.clone, core.clone.impls.CloneU64.clone,
    lift, bind_tc_ok]

theorem dpBudgetClone_id (d : obligation.DpBudget) :
    obligation.DpBudget.Insts.CoreCloneClone.clone d = ok d := rfl

theorem actionIdClone_id (a : obligation.ActionId) :
    obligation.ActionId.Insts.CoreCloneClone.clone a = ok a := by
  simp only [obligation.ActionId.Insts.CoreCloneClone.clone,
    vecClone_id core.clone.CloneU8 a (fun x _ => u8I_clone x), bind_tc_ok]

theorem labelClone_id (l : ifc.Label) :
    ifc.Label.Insts.CoreCloneClone.clone l = ok l := by
  simp only [ifc.Label.Insts.CoreCloneClone.clone,
    vecClone_id core.clone.CloneU32 l (fun x _ => u32I_clone x), bind_tc_ok]

theorem signatureClone_id (s : syntax.Signature) :
    syntax.Signature.Insts.CoreCloneClone.clone s = ok s := by
  simp only [syntax.Signature.Insts.CoreCloneClone.clone, core.clone.impls.CloneU8.clone,
    lift, vecClone_id core.clone.CloneU8 s.bytes (fun x _ => u8I_clone x), bind_tc_ok]

theorem principalIdClone_id (p : principal.PrincipalId) :
    principal.PrincipalId.Insts.CoreCloneClone.clone p = ok p := by
  simp only [principal.PrincipalId.Insts.CoreCloneClone.clone]
  rw [arrayClone_id core.clone.CloneU8 p (fun x _ => u8I_clone x)]; rfl

theorem principalClone_id (p : principal.Principal) :
    principal.Principal.Insts.CoreCloneClone.clone p = ok p := by
  induction p <;>
    simp only [principal.Principal.Insts.CoreCloneClone.clone, principalIdClone_id,
      bind_tc_ok, *]

theorem obligationClone_id (o : obligation.Obligation) :
    obligation.Obligation.Insts.CoreCloneClone.clone o = ok o := by
  induction o <;>
    simp only [obligation.Obligation.Insts.CoreCloneClone.clone, principalClone_id,
      actionIdClone_id, timeBoundClone_id, dpBudgetClone_id, bind_tc_ok, *]

theorem propClone_id (p : syntax.Prop) :
    syntax.Prop.Insts.CoreCloneClone.clone p = ok p := by
  induction p <;>
    simp only [syntax.Prop.Insts.CoreCloneClone.clone, principalClone_id, labelClone_id,
      obligationClone_id, timeBoundClone_id, core.clone.impls.CloneU32.clone, lift,
      bind_tc_ok, *]

/-- **★ The AST-wide clone-identity linchpin** for `syntax.Term`. -/
theorem termClone_id (t : syntax.Term) :
    syntax.Term.Insts.CoreCloneClone.clone t = ok t := by
  induction t <;>
    simp only [syntax.Term.Insts.CoreCloneClone.clone, propClone_id, principalClone_id,
      signatureClone_id, obligationClone_id, labelClone_id, timeBoundClone_id,
      core.clone.impls.CloneU32.clone, lift, bind_tc_ok, *]

end DLC.CloneId
