import DlcCore
import DLC.Decidability
import DLC.DecideDecode
import DLC.CtxWellFormed
import DLC.CloneId

/-!
# `infer_square` — the shipped Rust checker agrees with the hand mirror

Stage 1b+ of the verified certificate checker (`spec/r6.2-inc1-infer-square-design.md`): the
Aeneas image `decide.infer` of the Rust proof-checker corresponds to the hand `decideLean` under
the concrete decode (`DLC.DecideDecode`). Composed with T1 soundness this yields
`rust_decide_sound` — a green `cargo build` implies a real `Deriv`.

Built up from committable helper lemmas (this file grows as they land).
-/

namespace DLC.DecideSquare

open Aeneas Aeneas.Std Result
open dlc_core
open DLC.DecideDecode

/-- The additive-context slice lookup in `decide.infer`'s `Var` arm returns the option at the
raw index. This is the Aeneas `Slice.get` on the deref'd `additive` `Vec`, isolated so the var
arm can compose it with `List.getElem?_map` for the decode. -/
theorem additive_get (ctx : judgment.Ctx) (idx : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice syntax.Prop)
      (alloc.vec.Vec.deref ctx.additive) idx
      = ok (ctx.additive.val[idx.val]?) := by
  simp [core.slice.Slice.get, alloc.vec.Vec.deref]

/-- The decoded additive context's lookup is the decoded raw lookup: decode commutes with `[·]?`
on the additive `Vec` (`decCtx` maps `decProp` pointwise, so `List.getElem?_map`). -/
theorem getElem?_decCtx_additive (ctx : judgment.Ctx) (n : Nat) :
    (decCtx ctx).additive[n]? = (ctx.additive.val[n]?).map decProp := by
  show ((ctx.additive.val.map decProp)[n]?) = _
  simp [List.getElem?_map]

/-- Same for the linear context. -/
theorem getElem?_decCtx_linear (ctx : judgment.Ctx) (n : Nat) :
    (decCtx ctx).linear[n]? = (ctx.linear.val[n]?).map decProp := by
  show ((ctx.linear.val.map decProp)[n]?) = _
  simp [List.getElem?_map]

/-- The decoded linear context's length equals the raw length (decode is a pointwise `map`). -/
theorem decCtx_linear_length (ctx : judgment.Ctx) :
    (decCtx ctx).linear.length = ctx.linear.val.length := by
  show (ctx.linear.val.map decProp).length = _
  simp

/-- Decode an optional Aeneas prop to the hand world — the map used to state `infer_square`
(mirrors `shift_corr`'s `decTermC <$> …`). -/
abbrev decOptProp (o : Option syntax.Prop) : Option DLC.Prop' := o.map decProp

/-- The `U32 → Usize` index cast is value-preserving (widening: `32 ≤ 64`). -/
theorem cast_usize_val (i : Std.U32) : (UScalar.cast .Usize i).val = i.val := by
  simp only [UScalar.cast_val_eq]
  cases System.Platform.numBits_eq <;> simp_all <;> scalar_tac

/-- Result-functor map on `ok` (the `decOptProp <$> ok …` reduction). -/
@[simp] theorem decOptProp_map_ok (o : Option syntax.Prop) :
    decOptProp <$> (ok o : Result (Option syntax.Prop)) = ok (decOptProp o) := rfl

set_option maxHeartbeats 1000000 in
/-- ★ `Var` arm of `infer_square` (base case). -/
theorem infer_square_var (ctx : judgment.Ctx) (i : Std.U32) :
    decOptProp <$> decide.infer ctx (syntax.Term.Var i)
      = ok (decideLean (decCtx ctx) (DLC.Term.var i.val)) := by
  rw [decide.infer]
  have hidx := cast_usize_val i
  simp only [lift, bind_tc_ok, additive_get, decideLean, getElem?_decCtx_additive, hidx]
  cases h : ctx.additive.val[i.val]? with
  | some p =>
    simp only [Option.map_some, CloneId.propClone_id, bind_tc_ok]
    rfl
  | none =>
    simp only [Option.map_none, decCtx]
    -- linear fallback: decide.infer's len=1 / idx=0 if-tree vs decideLean's
    -- `match (linear.map decProp), i.val | [φ], 0 => some φ`.
    rcases hl : ctx.linear.val with _ | ⟨q, qs⟩
    · -- empty linear: len ≠ 1
      simp [hl, alloc.vec.Vec.len, decOptProp]
    · rcases qs with _ | ⟨q2, qs2⟩
      · -- singleton [q]: len = 1
        have h1 : ctx.linear.len = 1#usize := by
          simp only [alloc.vec.Vec.len]; scalar_tac
        rcases hi : i.val with _ | n
        · -- i.val = 0
          have h0 : UScalar.cast .Usize i = 0#usize := by scalar_tac
          simp only [h1, h0, if_true, reduceIte]
          simp [alloc.vec.Vec.index, alloc.vec.Vec.index_usize, Slice.index_usize, hl,
            CloneId.propClone_id, decOptProp_map_ok, decOptProp]
        · -- i.val = n+1 ≠ 0
          have h0 : ¬ (UScalar.cast .Usize i = 0#usize) := by scalar_tac
          simp [h1, h0, hl, decOptProp]
      · -- ≥2 elements: len ≠ 1
        simp [hl, alloc.vec.Vec.len, decOptProp]

end DLC.DecideSquare
