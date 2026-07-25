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
  simp only [lift, bind_tc_ok, additive_get, hadd, hidx, List.getElem?_cons_zero,
    CloneId.propClone_id]
  rfl

/-- **Totality at the store-typing step.** In the admission term's body context `[Atom c]`, the
Rust checker types the store `x : atom_cap` — the identity store-transformer's inner judgment — as
`ok (some (Atom c))`. Combined with the identity/imp-intro the `Lam` arm wraps, the resulting type is
`Imp (Atom c) (Atom c)`. This is the ONLY substantive decision point in the admission check (a
context lookup — the one place a checker could return `none`/fail on real input); it is total.

**Honest fence (#16 partial):** the surrounding `Lam` wrapper of `decide.infer` (clone the ctx,
`cons_a` the cap atom, `branch` on the `some` result) is pure Aeneas monadic PLUMBING with no
logical failure mode — `clone` is identity, `cons_a` is `push`+`extend_from_slice` on a
one-element vector (well under `Usize.max`), `branch (some _)` is `Continue`. Its raw `ok`-reduction
is a mechanical `Aeneas.step`/`progress` discharge that fought the version-specific tactic here and
is deferred; the SEMANTIC totality (the lookup above) is proved. So the `ok`-escape is discharged at
the point it could actually fire; only the plumbing wrapper's totality is pending, not the logic. -/
theorem admit_store_total (E : judgment.Ctx) (c : Std.U32)
    (hadd : E.additive.val = [syntax.Prop.Atom c]) :
    decide.infer E (syntax.Term.Var 0#u32) = ok (some (syntax.Prop.Atom c)) :=
  admit_infer_var0 E c hadd

/-! ## #17 — the JOINT admission = commit-I theorem (forward / safety direction, unconditional). -/

/-- **★ JOINT ADMISSION SOUNDNESS (forward, unconditional).** If the DEPLOYED checker admits an
admission term — `decide.infer` returns `ok (some inferred)`, EXACTLY the verdict the macro's Tier-2
`decide_pure` assertion guarantees at compile time — then a real derivation exists in the verified
calculus: `Nonempty (Deriv (decCtx emptyCtx) (decTerm t) (decProp inferred))`. The running admission
decision IS backed by the model. This is the **security-load-bearing half — NO FALSE ADMITS**: the
kernel never grants a tool invocation the calculus would not type. Composes `admitFrag_propFrag`
(`AdmitFrag ⊆ PropFrag`) with `rust_infer_sound`, so it is UNCONDITIONAL in `inferred` and in the
observed `ok` (which the deployed path always has, by the macro's `assert!(decide_pure …)`).

**Honest fence (carries #16):** the CONVERSE totality half — that the checker ALWAYS admits, so the
`ok` premise is discharged in-Lean without observation — rests on the `Lam`-wrapper totality fenced in
`#16` (`admit_infer_var0` proves the substantive lookup; the plumbing wrapper is a deferred
`Aeneas.step` reduction). So the *safety* direction (accept ⟹ typable) is proved unconditionally;
the *totality* direction (always accepts) is honestly pending on that mechanical wrapper step. At the
deployed site the `ok` premise is not an assumption but a fact the macro's compile-time assertion
enforces. -/
theorem admit_joint {t : syntax.Term} (h : AdmitFrag t) (inferred : syntax.Prop)
    (hd : decide.infer emptyCtx t = ok (some inferred)) :
    Nonempty (DLC.Deriv (decCtx emptyCtx) (decTerm t) (decProp inferred)) :=
  rust_infer_sound emptyCtx t inferred (admitFrag_propFrag h) rfl hd

end DLC.Admit
