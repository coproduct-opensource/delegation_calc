/-
DLC — Abstract syntax of propositions and proof terms.

The BNF this file encodes is frozen in `spec/syntax.md`. The Rust mirror is
`crates/dlc-core/src/syntax.rs`; Aeneas translates that Rust back into the
`DLC.Aeneas.DlcCore` namespace, and the function-correspondence theorem
(see `DLC.Decidability`) bridges this hand-written Lean to the Aeneas output.
-/

import DLC.Principal
import DLC.IFCLabel
import DLC.Obligation
import DLC.Time

namespace DLC

/-- Proposition forms — what a proof term proves. -/
inductive Prop' : Type where
  | top : Prop'
  | bot : Prop'
  | atom : Nat → Prop'
  | imp : Prop' → Prop' → Prop'
  | and : Prop' → Prop' → Prop'
  | or  : Prop' → Prop' → Prop'
  | says : Principal → Prop' → Prop'
  | speaksFor : Principal → Principal → Prop'
  | at : Prop' → Label → Prop'
  | boxed : Obligation → Prop' → Prop'
  | within : TimeBound → Prop' → Prop'
  | tensor : Prop' → Prop' → Prop'
  | lolli : Prop' → Prop' → Prop'
  /-- `Replicated φ` — the type of a value committed to the replicated log at
  store-type `φ` (DLC-D; `spec/distributed-calculus-design-2026-07.md` §2).
  Mirrors `Prop::Replicated` in `crates/dlc-core/src/syntax.rs`.

  Added 2026-07-23 (R1 first-classing, increment 1: pure syntax fan-out). A
  modality that recurses into `φ` as `says`/`within` do.

  Revised 2026-07-23 (R1-inc3): now LABEL-INDEXED (`Prop' → Label → Prop'`). The
  label was previously carried only by the `command` term; making it a type
  index is what lets the `runCmd` eliminator read `ℓ` off the value's type
  compositionally (DCC/Modal-Effect-Types discipline) and classify the run's
  result at `φ @ ℓ`. `commit-I` ties the term's label field to this index. -/
  | replicated : Prop' → Label → Prop'
  -- No `deriving Repr, DecidableEq` here: the constituent `Label` (alias for
  -- nucleus's Aeneas-generated `nucleus_ifc_kernel.CapabilityLattice`) does not
  -- carry derived instances. Equalities that need to be computed land via
  -- targeted `Decidable` instances at the use sites where they're needed.

/-- A cryptographic signature carried by `Sign` and `Verify` terms. -/
structure Signature where
  /-- Algorithm identifier (Ed25519 = 0). -/
  alg : UInt8
  /-- Raw signature bytes. -/
  bytes : List UInt8
  deriving Repr, DecidableEq

/-- Proof term forms. Variables are de-Bruijn indices. -/
inductive Term : Type where
  | var : Nat → Term
  | lam : Prop' → Term → Term
  | app : Term → Term → Term
  | sign : Principal → Term → Signature → Term
  | verify : Principal → Term → Signature → Term
  | delegate : Term → Term → Term
  | attenuate : Term → Prop' → Term
  /-- `box_O(M, N)` -- the `□_O φ` introduction form. The obligation is a
  TERM index, not merely a component of the typing derivation, mirroring
  `Term::Boxed` in `crates/dlc-core/src/syntax.rs` and the grammar in
  `spec/syntax.md`. This is what lets `pendingObligations : Term → List
  Obligation` (T4) read the obligation from syntax alone; while `boxI`
  concluded at `Term.app`, no term could carry an obligation and T4 was
  provably vacuous. See `spec/t4-obligation-design-2026-07.md`. -/
  | boxed : Obligation → Term → Term → Term
  | discharge : Term → Term → Term
  | liftLabel : Label → Term → Term
  | declassify : Label → Term → Term → Term
  | now : TimeBound → Term
  | withinIntro : TimeBound → Term → Term
  -- Additive product (`and`)
  | pair : Term → Term → Term
  | fst : Term → Term
  | snd : Term → Term
  -- Additive coproduct (`or`)
  | inl : Prop' → Term → Term
  | inr : Prop' → Term → Term
  | case : Term → Term → Term → Term
  -- Multiplicative product (linear tensor)
  | tensorIntro : Term → Term → Term
  | letTensor : Term → Term → Term
  -- Says-elimination forms
  /-- `says-E` — `let ⟨x⟩_p = M in N`, the spec's `saysBind_p(M, N)`
  (`spec/syntax.md`, `spec/typing-rules.md` §4). BINDS `x:φ` in the body, so
  `shift`/`substAt` bump under it. The conclusion PRESERVES the modality
  (`p says ψ`), which is what separates it from `letSays`.

  Added 2026-07-20: the rule concluded at `Term.app M N`, which is not a
  binder, so the cutoff was never bumped for the body and the says-E case of
  any shift lemma was off by one and unprovable. -/
  | saysBind : Principal → Term → Term → Term
  | letSays : Principal → Term → Term → Term
  | sfExtract : Term → Term
  /-- `command(M, c, ℓ)` — first-class replicated write (DLC-D;
  `spec/distributed-calculus-design-2026-07.md` §1). `M` is the store
  transformer, `c` is the capability CREDENTIAL SUBTERM (not a typing
  side-condition — the `boxed`/`sign` "obligation carried by the term"
  discipline), `ℓ` is the IFC label. Mirrors `Term::Command(Box<Term>,
  Box<Term>, Label)` in `crates/dlc-core/src/syntax.rs`.

  Added 2026-07-23 (R1 first-classing, increment 1: pure syntax fan-out).
  Neither subterm is a binder, so — like `app`/`pair`, unlike `saysBind`/
  `letTensor` — `shift`/`substAt` recurse into `M` and `c` WITHOUT bumping the
  cutoff; the label is untouched. INERT + UNTYPABLE this increment: `step`
  leaves it STUCK (`Value (command …) = false`), and there is NO `Deriv`/
  `PropDeriv`/inference rule that types it (`commit-I` is deferred). Because it
  is untypable, Progress / NonInterference / subject reduction and every other
  typing-derivation induction re-found for free. -/
  | command : Term → Term → Label → Term
  /-- `runCmd(V, s)` — the `Replicated` ELIMINATOR (DLC-D; R1-inc3). Runs the
  replicated store-transformer boxed in `V : Replicated (φ ⊃ φ) ℓ` against a
  store `s : φ`, classifying the result at `φ @ ℓ`. Mirrors `Term::RunCmd` in
  `crates/dlc-core/src/syntax.rs`.

  Added 2026-07-23 (R1-inc3). Neither subterm binds, so — like `app`/`command`,
  unlike `saysBind`/`letTensor` — `shift`/`substAt` recurse into both fields
  WITHOUT bumping the cutoff. Unlike `command`, `runCmd` is NOT a value: it is
  an eliminator that STEPS. `runCmd (command M c ℓ) s ▷ liftLabel ℓ (app M s)`
  (credential erased, label carried into the `liftLabel` wrapper); `ξ-runCmd`
  normalizes the scrutinee. -/
  | runCmd : Term → Term → Term
  -- No `deriving Repr, DecidableEq` here: the constituent `Label` (alias for
  -- nucleus's Aeneas-generated `nucleus_ifc_kernel.CapabilityLattice`) does not
  -- carry derived instances. Equalities that need to be computed land via
  -- targeted `Decidable` instances at the use sites where they're needed.

end DLC
