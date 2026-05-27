/-
§4.4 -- Protocol-Logic Correspondence theorem.

The Phase-2 keystone: connects Tamarin protocol traces to DLC derivations.
Composes the two halves:

  L2.3 (wire ↔ symbolic encoding):  models/tamarin/dlc.spthy facts ↔
                                     crates/dlc-protocol/src/wire.rs CBOR
  L2.5 (trace ↔ derivation):         List TraceEvent ↔ Deriv Γ M φ

Together they give T2's symbolic half (the computational half is L2.4's
EasyCrypt reduction).

Phase-2 plan reference: months 12-14 (L2.5); M2.M15 closure tag
`v1.5.0-phase2`. The full lifting proof is graduate-thesis-grade; this
file states the canonical form. The companion Rust runtime emits the
trace dump via `crates/dlc-protocol/src/{export_tamarin,export_proverif}.rs`.
-/

import DLC.Correspondence
import DLC.Judgment

namespace DLC

/-! ## Trace events mirroring the Tamarin model.

These are the events that the `models/tamarin/dlc.spthy` rules emit
during a run. The Lean enum mirrors them faithfully; the Rust
`dlc-protocol::export_tamarin::term_to_tamarin` emits the same set of
event tags as text lines, completing the operational picture. -/

inductive TraceEvent : Type where
  /-- `Says(P, prop)` — principal P signed proposition prop. -/
  | says : Principal → Prop' → TraceEvent
  /-- `SpeaksForIssued(P, Q)` — P issued a SpeaksFor naming Q. -/
  | speaksForIssued : Principal → Principal → TraceEvent
  /-- `DelegateAccept(P, Q, prop)` — verifier accepted (P acting Q) says prop. -/
  | delegateAccept : Principal → Principal → Prop' → TraceEvent
  /-- `LtkReveal(P)` — principal P's long-term key was revealed. -/
  | ltkReveal : Principal → TraceEvent

/-- A symbolic protocol trace: an ordered list of events. Timestamps are
implicit (= list index, ascending). -/
abbrev TamarinTrace := List TraceEvent

/-! ## L2.5 -- Lifting function (signature only).

The full body of `liftToDeriv` is the M2.M15 closure work. It walks the
trace events and reconstructs:
  * A context Γ from the Says and SpeaksForIssued events (each becomes
    an additive hypothesis at the corresponding `says φ` or
    `speaksFor q p` proposition).
  * A term M whose structure mirrors the trace's delegation chains.
  * A proposition φ matching the final DelegateAccept (or the singleton
    event if the trace doesn't end with a delegation).

The closure needs the substitution / subject-reduction proofs first.
Until then we expose just the signature so downstream consumers can
write code against it. -/

/-- Reconstruct a DLC derivation triple from a Tamarin trace. Returns
`none` if the trace is malformed (e.g. references an unobserved
principal). -/
opaque liftToDeriv : TamarinTrace → Option (Ctx × Term × Prop')

/-! ## L2.5 statement.

For every well-formed Tamarin trace, the lifted triple inhabits Deriv. -/

/-- A trace is well-formed if every DelegateAccept references principals
that earlier emitted both a SpeaksForIssued and a Says with the
matching proposition. The Tamarin non_splicing lemma already proves this
holds for any trace the model accepts -- L2.5 is the Lean-side mirror. -/
def TraceWellFormed (_t : TamarinTrace) : Prop :=
  -- Real body: requires walking the trace and checking the SpeaksForIssued
  -- /Says antecedents for each DelegateAccept. Stated as a Prop placeholder;
  -- body lands with the proof closure.
  True

/-- L2.5 -- Trace-to-derivation lifting statement. -/
def L2_5_TraceLiftingStatement : Prop :=
  ∀ (t : TamarinTrace),
    TraceWellFormed t →
    ∃ (Γ : Ctx) (M : Term) (φ : Prop'),
      liftToDeriv t = some (Γ, M, φ) ∧
      Nonempty (Deriv Γ M φ)

/-! ## §4.4 -- Composed correspondence.

Composes L2.3 (round-trip) with L2.5 (lifting). Given a Tamarin trace,
this lifts to a DLC derivation, and the wire encoding of that derivation
round-trips losslessly. The composition is the symbolic half of T2; the
full T2 layers L2.4's EasyCrypt computational bridge on top. -/

/-- §4.4 -- Protocol-logic correspondence (statement). -/
def ProtocolLogicCorrespondenceStatement : Prop :=
  ∀ (t : TamarinTrace),
    TraceWellFormed t →
    ∃ (Γ : Ctx) (M : Term) (φ : Prop'),
      liftToDeriv t = some (Γ, M, φ) ∧
      Nonempty (Deriv Γ M φ) ∧
      WireRoundTripStatement

/-! ## Backward-compat alias. -/

/-- The original stub. Kept as `abbrev` for any reference to the old name. -/
abbrev protocol_correspondence_stub : True := trivial

end DLC
