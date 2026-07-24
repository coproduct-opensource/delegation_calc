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

/-- The additive/linear context slices clone to themselves (props are clone-identity),
as a rewrite the `cons_a`/`cons_l` reductions can fire. -/
@[simp] theorem sliceClone_id_prop (s : Slice syntax.Prop) :
    Slice.clone syntax.Prop.Insts.CoreCloneClone.clone s = ok s :=
  CloneId.sliceClone_id syntax.Prop.Insts.CoreCloneClone s (fun x _ => CloneId.propClone_id x)

/-- Invert an `ok`-terminating monadic bind: if `(do let x ← m; f x) = ok y`, then `m`
succeeded and its continuation on that value also reached `ok y`. (The `Result` twin of
`map_ok_inv`; used to peel `cons_a`'s two binds without `split` reaching under the `let`.) -/
private theorem bind_ok_inv {α β} {m : Result α} {f : α → Result β} {y : β}
    (h : (do let x ← m; f x) = ok y) : ∃ x, m = ok x ∧ f x = ok y := by
  cases m with
  | ok x => exact ⟨x, rfl, by simpa using h⟩
  | fail e => simp at h
  | div => simp at h

/-- Success spec for the additive/linear `extend_from_slice`: since every `Prop` clones to
itself, a successful append yields exactly `v ++ s`. The dependent `Slice.clone` match sits
at head position here (`extend_from_slice`'s body is `if … then match … else …`), so `split`
can reduce it — unlike inside `cons_a`'s bind chain. -/
theorem extend_from_slice_prop_ok (v : alloc.vec.Vec syntax.Prop) (s : Slice syntax.Prop)
    (v1 : alloc.vec.Vec syntax.Prop)
    (h : alloc.vec.Vec.extend_from_slice syntax.Prop.Insts.CoreCloneClone v s = ok v1) :
    v1.val = v.val ++ s.val := by
  rw [alloc.vec.Vec.extend_from_slice] at h
  split at h
  · split at h
    · rename_i s' hcl
      rw [sliceClone_id_prop] at hcl; injection hcl with hcl; subst hcl
      injection h with h; subst h; rfl
    · rename_i e hcl; rw [sliceClone_id_prop] at hcl; exact absurd hcl (by simp)
    · rename_i hcl; rw [sliceClone_id_prop] at hcl; exact absurd hcl (by simp)
  · exact absurd h (by simp)

/-- **★ Success-path `cons_a` spec.** If the faithful `cons_a` (`push` +
`extend_from_slice`, the Aeneas-faithful prepend) *succeeds*, its decoded result is the
hand `consA` prepend. Crucially there is **no `Usize.max` overflow hypothesis**: a
successful `cons_a` already witnesses that the `extend_from_slice` length guard passed
(the `else fail` branch contradicts `= ok ext`). This is exactly what the forward
`infer_square`'s `Lam`/`Case` arms need — they only fire on the success path of
`decide.infer`, where `cons_a` provably succeeded. -/
theorem decCtx_cons_a_ok (c : judgment.Ctx) (phi : syntax.Prop) (ext : judgment.Ctx)
    (h : judgment.Ctx.cons_a c phi = ok ext) :
    decCtx ext = DLC.Ctx.consA (decProp phi) (decCtx c) := by
  rw [judgment.Ctx.cons_a] at h
  obtain ⟨v, hv, h⟩ := bind_ok_inv h
  obtain ⟨v1, hv1, h⟩ := bind_ok_inv h
  injection h with h; subst h
  have hval : v1.val = v.val ++ c.additive.val :=
    extend_from_slice_prop_ok _ _ _ hv1
  have hvval : v.val = [phi] := by
    rw [alloc.vec.Vec.push, alloc.vec.Vec.new] at hv
    split at hv
    · injection hv with hv; subst hv; simp [List.concat_eq_append]
    · exact absurd hv (by simp)
  simp [decCtx, DLC.Ctx.consA, hval, hvval]

/-! ## Forward per-arm agreement (the `infer_square` capstone, fragment-scoped)

Each lemma below shows: whenever the shipped Rust checker `decide.infer` types an arm (in ANY
context), the verified `decideLean` types the decoded term at the decoded type. Stated as
`FwdAgree`, ∀-over-context so binder arms can instantiate a sub-term's IH at an extended context.
Assembled by induction (with a `PropFrag` predicate excluding the four arms where `decide.infer`
is deliberately more permissive — see `spec/r6.2-inc1-infer-square-design.md` §6). -/

/-- `?`-operator `branch` on `Option` (both reductions are `rfl`) — as simp lemmas so a
`decide.infer` arm's `let cf ← branch o; match cf …` peels once `o` is `some`/`none`. -/
@[simp] theorem branch_some {T} (v : T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (some v)
      = ok (core.ops.control_flow.ControlFlow.Continue v) := rfl

@[simp] theorem branch_none {T} :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (none : Option T)
      = ok (core.ops.control_flow.ControlFlow.Break none) := rfl

/-- Forward per-arm agreement for a single term (∀ context / inferred type). -/
abbrev FwdAgree (term : syntax.Term) : Prop :=
  ∀ (ctx : judgment.Ctx) (inferred : syntax.Prop),
    decide.infer ctx term = ok (some inferred) →
    decideLean (decCtx ctx) (decTerm term) = some (decProp inferred)

/-- `now τ` — introduces `Top` in any context; both checkers agree. -/
theorem fwd_now (t : time.TimeBound) : FwdAgree (syntax.Term.Now t) := by
  intro ctx inferred h
  rw [decide.infer] at h
  injection h with h; injection h with h; subst h
  rfl

/-- `sign p m _` — `M : φ ⟹ p says φ`; agrees given the sub-term `m` agrees. -/
theorem fwd_sign (p : principal.Principal) (m : syntax.Term) (sig : syntax.Signature)
    (ih : FwdAgree m) : FwdAgree (syntax.Term.Sign p m sig) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none =>
    simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, CloneId.principalClone_id, bind_tc_ok] at h
    injection h with h; injection h with h; subst h
    simp only [decTerm, decProp, decideLean, ih ctx val ho]

/-- `inl ψ m` — `M : φ ⟹ φ ∨ ψ`; agrees given `m` agrees (clones the injected `other`). -/
theorem fwd_inl (other : syntax.Prop) (m : syntax.Term) (ih : FwdAgree m) :
    FwdAgree (syntax.Term.Inl other m) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, CloneId.propClone_id, bind_tc_ok] at h
    injection h with h; injection h with h; subst h
    simp only [decTerm, decProp, decideLean, ih ctx val ho]

/-- `inr φ m` — `M : ψ ⟹ φ ∨ ψ`. -/
theorem fwd_inr (other : syntax.Prop) (m : syntax.Term) (ih : FwdAgree m) :
    FwdAgree (syntax.Term.Inr other m) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, CloneId.propClone_id, bind_tc_ok] at h
    injection h with h; injection h with h; subst h
    simp only [decTerm, decProp, decideLean, ih ctx val ho]

/-- `within_intro τ m` — `M : φ ⟹ within τ φ` (clones the time bound). -/
theorem fwd_withinIntro (tau : time.TimeBound) (m : syntax.Term) (ih : FwdAgree m) :
    FwdAgree (syntax.Term.WithinIntro tau m) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, CloneId.timeBoundClone_id, bind_tc_ok] at h
    injection h with h; injection h with h; subst h
    simp only [decTerm, decProp, decideLean, ih ctx val ho]

/-- `lift_ℓ m` — introduces the IFC `at` modality; BOTH checkers agree (`decideLean`
produces `at φ ℓ`, contrary to the retracted "label-free" invariant). Clones the label. -/
theorem fwd_liftLabel (label : ifc.Label) (m : syntax.Term) (ih : FwdAgree m) :
    FwdAgree (syntax.Term.LiftLabel label m) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, CloneId.labelClone_id, bind_tc_ok] at h
    injection h with h; injection h with h; subst h
    simp only [decTerm, decProp, decideLean, ih ctx val ho]

/-- `pair a b` — `A : φ, B : ψ ⟹ φ ∧ ψ`; agrees given both sub-terms agree. -/
theorem fwd_pair (a b : syntax.Term) (iha : FwdAgree a) (ihb : FwdAgree b) :
    FwdAgree (syntax.Term.Pair a b) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, bind_tc_ok] at h
    obtain ⟨o1, ho1, h⟩ := bind_ok_inv h
    cases o1 with
    | none => simp [branch_none, bind_tc_ok,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
    | some val1 =>
      simp only [branch_some, bind_tc_ok] at h
      injection h with h; injection h with h; subst h
      simp only [decTerm, decProp, decideLean, iha ctx val ho, ihb ctx val1 ho1]

/-- `tensor_intro a b` — `A : φ, B : ψ ⟹ φ ⊗ ψ`. -/
theorem fwd_tensorIntro (a b : syntax.Term) (iha : FwdAgree a) (ihb : FwdAgree b) :
    FwdAgree (syntax.Term.TensorIntro a b) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, bind_tc_ok] at h
    obtain ⟨o1, ho1, h⟩ := bind_ok_inv h
    cases o1 with
    | none => simp [branch_none, bind_tc_ok,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
    | some val1 =>
      simp only [branch_some, bind_tc_ok] at h
      injection h with h; injection h with h; subst h
      simp only [decTerm, decProp, decideLean, iha ctx val ho, ihb ctx val1 ho1]

/-- `fst m` — `M : φ ∧ ψ ⟹ φ`. The inferred sub-type is matched: only `And` types. -/
theorem fwd_fst (m : syntax.Term) (ih : FwdAgree m) : FwdAgree (syntax.Term.Fst m) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, bind_tc_ok] at h
    cases val with
    | And phi psi =>
      dsimp only at h; injection h with h; injection h with h; subst h
      simp only [decTerm, decProp, decideLean, ih ctx (syntax.Prop.And phi psi) ho]
    | _ => simp at h

/-- `snd m` — `M : φ ∧ ψ ⟹ ψ`. -/
theorem fwd_snd (m : syntax.Term) (ih : FwdAgree m) : FwdAgree (syntax.Term.Snd m) := by
  intro ctx inferred h
  rw [decide.infer] at h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, bind_tc_ok] at h
    cases val with
    | And phi psi =>
      dsimp only at h; injection h with h; injection h with h; subst h
      simp only [decTerm, decProp, decideLean, ih ctx (syntax.Prop.And phi psi) ho]
    | _ => simp at h

/-- `lam φ body` — `body : ψ in (φ :: Γ) ⟹ φ ⊃ ψ`. The first BINDER arm: `decide.infer`
clones the context and `φ`, extends via the faithful `cons_a`, and recurses; the decoded
extension is `consA (decProp φ) (decCtx ctx)` by `decCtx_cons_a_ok` (success path). -/
theorem fwd_lam (phi : syntax.Prop) (body : syntax.Term) (ih : FwdAgree body) :
    FwdAgree (syntax.Term.Lam phi body) := by
  intro ctx inferred h
  rw [decide.infer] at h
  simp only [CloneId.ctxClone_id, CloneId.propClone_id, bind_tc_ok] at h
  obtain ⟨extended, hext, h⟩ := bind_ok_inv h
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  cases o with
  | none => simp [branch_none, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at h
  | some val =>
    simp only [branch_some, bind_tc_ok] at h
    injection h with h; injection h with h; subst h
    have key := ih extended val ho
    rw [decCtx_cons_a_ok ctx phi extended hext] at key
    simp only [decTerm, decProp, decideLean, key]

/-- `var i` — reuse the full-equality `infer_square_var` (the base case). -/
theorem fwd_var (i : Std.U32) : FwdAgree (syntax.Term.Var i) := by
  intro ctx inferred h
  have hsq := infer_square_var ctx i
  rw [h] at hsq
  simp only [decOptProp_map_ok, decOptProp, Option.map_some] at hsq
  injection hsq with hsq
  simp only [decTerm]
  exact hsq.symm

/-! ## The agreeing fragment and its assembled `infer_square`

`PropFrag` carves the currently-verified agreeing fragment of `F` — the constructors whose
`fwd_*` arm lemma is proven. It EXCLUDES the five disagreeing arms
(`boxed/saysBind/attenuate/declassify/letTensor`) AND, for now, the arms still awaiting their
`eq`-soundness lemmas (`app/verify/command/runCmd/case/letSays/delegate/sfExtract`) — those grow
`PropFrag` as they land. Assembling now locks the end-to-end result and de-risks the induction. -/
inductive PropFrag : syntax.Term → Prop where
  | var (i) : PropFrag (syntax.Term.Var i)
  | now (t) : PropFrag (syntax.Term.Now t)
  | sign (p m sig) : PropFrag m → PropFrag (syntax.Term.Sign p m sig)
  | inl (o m) : PropFrag m → PropFrag (syntax.Term.Inl o m)
  | inr (o m) : PropFrag m → PropFrag (syntax.Term.Inr o m)
  | withinIntro (t m) : PropFrag m → PropFrag (syntax.Term.WithinIntro t m)
  | liftLabel (l m) : PropFrag m → PropFrag (syntax.Term.LiftLabel l m)
  | pair (a b) : PropFrag a → PropFrag b → PropFrag (syntax.Term.Pair a b)
  | tensorIntro (a b) : PropFrag a → PropFrag b → PropFrag (syntax.Term.TensorIntro a b)
  | fst (m) : PropFrag m → PropFrag (syntax.Term.Fst m)
  | snd (m) : PropFrag m → PropFrag (syntax.Term.Snd m)
  | lam (phi body) : PropFrag body → PropFrag (syntax.Term.Lam phi body)

/-- **★ Assembled forward `infer_square` on the fragment.** For every `PropFrag` term, the shipped
Rust checker's positive verdicts are backed by the verified `decideLean`. Inducts on the `PropFrag`
derivation, discharging each case by its `fwd_*` arm lemma (the sub-term IHs are `FwdAgree`). -/
theorem infer_square_frag (term : syntax.Term) (hpf : PropFrag term) : FwdAgree term := by
  induction hpf with
  | var i => exact fwd_var i
  | now t => exact fwd_now t
  | sign p m sig _ ih => exact fwd_sign p m sig ih
  | inl o m _ ih => exact fwd_inl o m ih
  | inr o m _ ih => exact fwd_inr o m ih
  | withinIntro t m _ ih => exact fwd_withinIntro t m ih
  | liftLabel l m _ ih => exact fwd_liftLabel l m ih
  | pair a b _ _ iha ihb => exact fwd_pair a b iha ihb
  | tensorIntro a b _ _ iha ihb => exact fwd_tensorIntro a b iha ihb
  | fst m _ ih => exact fwd_fst m ih
  | snd m _ ih => exact fwd_snd m ih
  | lam phi body _ ih => exact fwd_lam phi body ih

/-- Every `PropFrag` term decodes to a `Term.isPropositional` term — so T1
(`t1_propositional_soundness`, which needs `isPropositional`) applies to the whole fragment
(`isPropositional` = every constructor except the distributed `command`/`runCmd`). -/
theorem propFrag_isPropositional (term : syntax.Term) (hpf : PropFrag term) :
    (decTerm term).isPropositional = true := by
  induction hpf with
  | var i => rfl
  | now t => rfl
  | sign p m sig _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | inl o m _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | inr o m _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | withinIntro t m _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | liftLabel l m _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | pair a b _ _ iha ihb =>
    simp only [decTerm, DLC.Term.isPropositional, iha, ihb, Bool.and_self]
  | tensorIntro a b _ _ iha ihb =>
    simp only [decTerm, DLC.Term.isPropositional, iha, ihb, Bool.and_self]
  | fst m _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | snd m _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih
  | lam phi body _ ih => simpa only [decTerm, DLC.Term.isPropositional] using ih

/-- **★ Verified inference soundness.** If the shipped Rust checker `decide.infer` INFERS a type
for a fragment term in an empty-linear context, that type is genuinely derivable — a real `Deriv`.
Chains the assembled `infer_square_frag` (checker ≡ verified `decideLean`) with T1 soundness
(`decideLean = some ⟹ Nonempty Deriv`). This is the "a green build carries a proof" guarantee for
the agreeing fragment, stated for the inferred type (no `eq`-soundness lemma needed). -/
theorem rust_infer_sound (ctx : judgment.Ctx) (term : syntax.Term) (inferred : syntax.Prop)
    (hpf : PropFrag term) (hlin : ctx.linear.val = [])
    (h : decide.infer ctx term = ok (some inferred)) :
    Nonempty (DLC.Deriv (decCtx ctx) (decTerm term) (decProp inferred)) := by
  have hagree := infer_square_frag term hpf ctx inferred h
  have hprop := propFrag_isPropositional term hpf
  have hctx : decCtx ctx = { additive := ctx.additive.val.map decProp, linear := [] } := by
    simp only [decCtx, hlin, List.map_nil]
  rw [hctx] at hagree ⊢
  exact t1_propositional_soundness (decTerm term) (ctx.additive.val.map decProp)
    (decProp inferred) hprop hagree

/-- The empty typing context (both zones empty). -/
abbrev emptyCtx : judgment.Ctx :=
  ⟨alloc.vec.Vec.new syntax.Prop, alloc.vec.Vec.new syntax.Prop⟩

/-- **Anti-vacuity witness (leaf).** `decide.infer` really accepts `now τ` at `Top`, and
`rust_infer_sound` really hands back a `Deriv` — the milestone theorem's hypotheses are
satisfiable by a concrete term, so it is NOT vacuously true. -/
theorem rust_infer_sound_witness_now :
    Nonempty (DLC.Deriv (decCtx emptyCtx) (decTerm (syntax.Term.Now ⟨0#u64⟩))
      (decProp syntax.Prop.Top)) :=
  rust_infer_sound emptyCtx (syntax.Term.Now ⟨0#u64⟩) syntax.Prop.Top
    (PropFrag.now _) rfl (by simp only [decide.infer])

end DLC.DecideSquare
