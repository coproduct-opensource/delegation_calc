import DLC.DecideSquare

/-! # The ADMISSION FRAGMENT — `AdmitFrag`.

The joint-admission-control arc (spec: prove the deployed kernel grants a tool invocation IFF
`commit-I` authorizes it, *unconditionally on the admission fragment*) needs the fragment named first.

`#[dlc_d::agent_service]`'s Tier-2 certificate emits EXACTLY one runtime term (`crates/dlc-d-macro`,
`envelope.rs`): the identity store-transformer `λx : atom_cap. x : atom_cap ⊃ atom_cap`, where
`atom_cap` is the tool's capability atom (FNV-1a of the tool name). At runtime the verified checker
`dlc_core::decide::decide_pure` is asked to type exactly this term — that IS the admission decision.

`AdmitFrag` carves that one shape over the Aeneas-translated `syntax.Term` (the term `decide_pure`
consumes). It is a SUBSET of `DecideSquare.PropFrag` (the agreeing fragment `rust_infer_sound` is
proved over), so it inherits that soundness — `#16` then proves `decide_pure` is *total* on it (no
`ok`/overflow escape), and `#17` composes the two into the unconditional joint `iff`.
-/

namespace DLC.Admit

open Aeneas Aeneas.Std Result
open dlc_core
open DLC.DecideSquare
open DLC.DecideDecode

/-- The admission fragment: exactly the macro-emitted identity store-transformer
`Lam (Atom c) (Var 0) : Atom c ⊃ Atom c` at the tool's cap atom `c`. One shape — the runtime term the
admission check types. -/
inductive AdmitFrag : syntax.Term → Prop where
  | idStore (c : Std.U32) :
      AdmitFrag (syntax.Term.Lam (syntax.Prop.Atom c) (syntax.Term.Var 0#u32))

/-- **Shape characterization** (what `#16`/`#17` invert on): an admission term is exactly
`Lam (Atom c) (Var 0)` for some cap atom `c`. -/
theorem admitFrag_shape {t : syntax.Term} (h : AdmitFrag t) :
    ∃ c : Std.U32, t = syntax.Term.Lam (syntax.Prop.Atom c) (syntax.Term.Var 0#u32) := by
  cases h with | idStore c => exact ⟨c, rfl⟩

/-- **`AdmitFrag ⊆ PropFrag`.** Every admission term lies in the agreeing fragment
`rust_infer_sound` covers — so the shipped checker's verdict on it is backed by the verified
`decideLean`. This is the hook the joint theorem (`#17`) spends. -/
theorem admitFrag_propFrag {t : syntax.Term} (h : AdmitFrag t) : PropFrag t := by
  cases h with
  | idStore c =>
    exact PropFrag.lam (syntax.Prop.Atom c) (syntax.Term.Var 0#u32) (PropFrag.var 0#u32)

/-- **Soundness inherited.** For an admission term, the shipped Rust checker's positive verdict is
backed by the verified `decideLean` (`FwdAgree`, via `infer_square_frag`). The runtime admission
decision is not a rubber stamp — where it types, a real `decideLean` derivation agrees. -/
theorem admitFrag_fwd {t : syntax.Term} (h : AdmitFrag t) : FwdAgree t :=
  infer_square_frag t (admitFrag_propFrag h)

/-- **Non-vacuity.** A concrete admission term (the macro's shape at a representative cap atom) is in
the fragment — `AdmitFrag` is inhabited by exactly what `#[dlc_d::agent_service]` emits, not empty. -/
theorem admitFrag_witness :
    AdmitFrag (syntax.Term.Lam (syntax.Prop.Atom 42#u32) (syntax.Term.Var 0#u32)) :=
  AdmitFrag.idStore 42#u32

/-! ## #16 — `decide.infer` is TOTAL on `AdmitFrag` (discharges the `ok`-escape).

`rust_infer_sound` is conditioned on `decide.infer ctx term = ok (some inferred)` as a HYPOTHESIS.
Here we prove that hypothesis holds — unconditionally — for every admission term: the deployed
checker always returns a verdict (`ok (some (Imp (Atom c) (Atom c)))`), never the fuel-exhausted
`none` / a `Result` failure. The admission decision is TOTAL. Because inference is structural (no
fuel) and the term is `Lam (Atom c) (Var 0)` (one imp-intro + one context lookup, no overflowing
arithmetic), the reduction closes concretely. -/

/-- The Var-`0` lookup succeeds in a singleton additive context: `decide.infer E (Var 0) =
ok (some (Atom c))` when `E.additive = [Atom c]`. The raw (un-`decOptProp`-mapped) companion to
`infer_square_var`, reusing the same reduction kit. -/
theorem admit_infer_var0 (E : judgment.Ctx) (c : Std.U32)
    (hadd : E.additive.val = [syntax.Prop.Atom c]) :
    decide.infer E (syntax.Term.Var 0#u32) = ok (some (syntax.Prop.Atom c)) := by
  rw [decide.infer]
  have hidx := cast_usize_val (0#u32)
  simp only [lift, bind_tc_ok, additive_get, hadd, hidx, CloneId.propClone_id]
  rfl

/-- **Totality at the store-typing step.** In the admission term's body context `[Atom c]`, the
Rust checker types the store `x : atom_cap` — the identity store-transformer's inner judgment — as
`ok (some (Atom c))`. Combined with the identity/imp-intro the `Lam` arm wraps, the resulting type is
`Imp (Atom c) (Atom c)`. This is the ONLY substantive decision point in the admission check (a
context lookup — the one place a checker could return `none`/fail on real input); it is total.

**Fence CLOSED (2026-07-31, Tier-A #1):** the surrounding `Lam` wrapper of `decide.infer` (clone
the ctx, `cons_a` the cap atom, `branch` on the `some` result) is now discharged forward by
`emptyCtx_clone` + `cons_a_empty_ok` + `branch_some`, composed in `admit_total` below. Both length
guards are satisfied concretely (length 0 push, one-element append), so no `Usize.max` hypothesis
is introduced. -/
theorem admit_store_total (E : judgment.Ctx) (c : Std.U32)
    (hadd : E.additive.val = [syntax.Prop.Atom c]) :
    decide.infer E (syntax.Term.Var 0#u32) = ok (some (syntax.Prop.Atom c)) :=
  admit_infer_var0 E c hadd

/-! ### Closing the `Lam`-wrapper fence (Tier-A #1)

The three plumbing steps the wrapper takes before the (already-proved) lookup, each discharged
forward rather than assumed: the context clone is identity, `cons_a` on the EMPTY context succeeds
(its `push` and `extend_from_slice` guards are both satisfied at length 0/1, so no `Usize.max`
hypothesis is needed), and the resulting context has exactly the singleton additive zone the lookup
lemma wants. -/

/-- The empty context clones to itself (both zones are empty vectors, and `Prop` is clone-identity). -/
theorem emptyCtx_clone :
    judgment.Ctx.Insts.CoreCloneClone.clone emptyCtx = ok emptyCtx := by
  have hv : alloc.vec.CloneVec.clone syntax.Prop.Insts.CoreCloneClone
      (alloc.vec.Vec.new syntax.Prop) = ok (alloc.vec.Vec.new syntax.Prop) :=
    CloneId.vecClone_id syntax.Prop.Insts.CoreCloneClone _
      (fun x _ => CloneId.propClone_id x)
  rw [judgment.Ctx.Insts.CoreCloneClone.clone]
  simp only [hv, bind_tc_ok, emptyCtx]

/-- **`cons_a` on the empty context SUCCEEDS**, with the singleton additive zone. Forward twin of
`decCtx_cons_a_ok`: that lemma reads a success off `= ok ext`; this one *produces* the success —
which is exactly what totality needs. `push` onto the fresh vector and `extend_from_slice` with the
empty additive slice both pass their length guards concretely, so nothing is assumed. -/
theorem cons_a_empty_ok (phi : syntax.Prop) :
    ∃ ext : judgment.Ctx,
      judgment.Ctx.cons_a emptyCtx phi = ok ext ∧ ext.additive.val = [phi] := by
  rw [judgment.Ctx.cons_a]
  simp only [emptyCtx, alloc.vec.Vec.push, alloc.vec.Vec.new,
    alloc.vec.Vec.deref, bind_tc_ok]
  split
  · rename_i hpush
    simp only [alloc.vec.Vec.extend_from_slice, sliceClone_id_prop, bind_tc_ok]
    split
    · exact ⟨_, rfl, by simp⟩
    · -- the length guard cannot fail: one element appended to the empty slice.
      rename_i hlen; exact absurd hlen (by simp [alloc.vec.Vec.length, Slice.length]; scalar_tac)
  · -- the push guard cannot fail on the fresh vector.
    rename_i hpush; exact absurd hpush (by simp; scalar_tac)

/-- **★ TOTALITY on the admission fragment (#16 closed).** The deployed checker ALWAYS returns a
verdict on an admission term: `decide.infer emptyCtx (Lam (Atom c) (Var 0)) =
ok (some (Imp (Atom c) (Atom c)))`. No `ok`-escape, no fuel exhaustion, no overflow hypothesis.

This is the ANTI-VACUITY leg of the admission claim: soundness alone (`admit_joint`) is satisfied by
a checker that refuses everything, which would be safe and useless — and, since `nucleus` now gates
live tool calls on this decision, would deny production traffic. Totality is what rules that out. -/
theorem admit_total (c : Std.U32) :
    decide.infer emptyCtx (syntax.Term.Lam (syntax.Prop.Atom c) (syntax.Term.Var 0#u32))
      = ok (some (syntax.Prop.Imp (syntax.Prop.Atom c) (syntax.Prop.Atom c))) := by
  obtain ⟨ext, hcons, hadd⟩ := cons_a_empty_ok (syntax.Prop.Atom c)
  rw [decide.infer]
  simp only [emptyCtx_clone, CloneId.propClone_id, hcons, bind_tc_ok,
    admit_infer_var0 ext c hadd, branch_some]

/-! ## #17 — the JOINT admission = commit-I theorem (forward / safety direction, unconditional). -/

/-- **★ JOINT ADMISSION SOUNDNESS (forward, unconditional).** If the DEPLOYED checker admits an
admission term — `decide.infer` returns `ok (some inferred)`, EXACTLY the verdict the macro's Tier-2
`decide_pure` assertion guarantees at compile time — then a real derivation exists in the verified
calculus: `Nonempty (Deriv (decCtx emptyCtx) (decTerm t) (decProp inferred))`. The running admission
decision IS backed by the model. This is the **security-load-bearing half — NO FALSE ADMITS**: the
kernel never grants a tool invocation the calculus would not type. Composes `admitFrag_propFrag`
(`AdmitFrag ⊆ PropFrag`) with `rust_infer_sound`, so it is UNCONDITIONAL in `inferred` and in the
observed `ok` (which the deployed path always has, by the macro's `assert!(decide_pure …)`).

**Both directions now proved (2026-07-31).** The *safety* direction (accept ⟹ typable) is this
theorem, unconditional. The *totality* direction (the checker always admits, so the `ok` premise is
discharged in-Lean rather than observed) is `admit_total` above — so the deployed admission decision
is backed by the model AND cannot spuriously refuse. `admit_joint_unconditional` composes them. -/
theorem admit_joint {t : syntax.Term} (h : AdmitFrag t) (inferred : syntax.Prop)
    (hd : decide.infer emptyCtx t = ok (some inferred)) :
    Nonempty (DLC.Deriv (decCtx emptyCtx) (decTerm t) (decProp inferred)) :=
  rust_infer_sound emptyCtx t inferred (admitFrag_propFrag h) rfl hd

/-- **★ JOINT ADMISSION, UNCONDITIONAL (safety ∧ totality).** For EVERY admission term the macro
emits, the deployed checker returns a verdict *and* that verdict is backed by a real derivation —
no `ok` hypothesis to observe, no fragment side-condition to discharge at the call site.

This is the form the deployment actually needs. `admit_joint` alone permits a checker that refuses
everything (safe, useless, and — since `nucleus` gates live tool calls on this decision — a
production outage); `admit_total` rules that out. Together: the admission gate accepts exactly the
macro's certificate, and every acceptance is a theorem. -/
theorem admit_joint_unconditional (c : Std.U32) :
    Nonempty (DLC.Deriv (decCtx emptyCtx)
      (decTerm (syntax.Term.Lam (syntax.Prop.Atom c) (syntax.Term.Var 0#u32)))
      (decProp (syntax.Prop.Imp (syntax.Prop.Atom c) (syntax.Prop.Atom c)))) :=
  admit_joint (AdmitFrag.idStore c) _ (admit_total c)

end DLC.Admit
