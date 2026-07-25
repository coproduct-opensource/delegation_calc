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

open Aeneas Aeneas.Std
open dlc_core
open DLC.DecideSquare

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

end DLC.Admit
