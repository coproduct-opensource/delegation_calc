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
  -- No `deriving Repr, DecidableEq` here: the constituent `Label` (alias for
  -- nucleus's Aeneas-generated `portcullis_core.CapabilityLattice`) does not
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
  | letSays : Principal → Term → Term → Term
  | sfExtract : Term → Term
  -- No `deriving Repr, DecidableEq` here: the constituent `Label` (alias for
  -- nucleus's Aeneas-generated `portcullis_core.CapabilityLattice`) does not
  -- carry derived instances. Equalities that need to be computed land via
  -- targeted `Decidable` instances at the use sites where they're needed.

end DLC
