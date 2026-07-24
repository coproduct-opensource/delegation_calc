import DlcCore
import DLC.Decidability
import DLC.DecideDecode
import DLC.CtxWellFormed

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

end DLC.DecideSquare
