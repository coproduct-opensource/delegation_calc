/-
§4.4 -- Protocol-Logic Correspondence theorem.

Connects Tamarin protocol traces to DLC derivations. The intended
composition has two halves:

  L2.3 (wire ↔ symbolic encoding):  models/tamarin/dlc.spthy facts ↔
                                     crates/dlc-protocol/src/wire.rs CBOR
  L2.5 (trace ↔ derivation):         List TraceEvent ↔ Deriv Γ M φ

STATUS (2026-07): only a restricted L2.5 is proven (singleton-trace
shape; see `l2_5_trace_lifting`). L2.3 has no Lean-side statement yet
(the former identity-serializer witness was vacuous and is deleted),
and the intended computational half — L2.4's EasyCrypt reduction —
does not exist (skeleton with a placeholder axiom encoding nothing).

Phase-2 plan reference: months 12-14 (L2.5); M2.M15 closure tag
`v1.5.0-phase2`. The full lifting proof is graduate-thesis-grade; this
file states the canonical form. The companion Rust runtime emits the
trace dump via `crates/dlc-protocol/src/{export_tamarin,export_proverif}.rs`.
-/

import DLC.Correspondence
import DLC.Judgment

namespace DLC

/-! ## L2.3 -- Wire round-trip statement.

Carried over from the L2.3 PR (PR #19). The Rust round-trip is
evidenced operationally by 25 unit tests in
`crates/dlc-protocol/src/wire.rs`;
the Lean statement here is what the Aeneas function-correspondence
theorem will close once `wire.rs` is extracted. -/

/-- The round-trip *property* on a given encoder/decoder pair: for every
term `M`, decoding its encoding yields `some M`. -/
def WireRoundTripProperty
    {Bytes : Type}
    (encode : Term → Bytes)
    (decode : Bytes → Option Term) : Prop :=
  ∀ M : Term, decode (encode M) = some M

/-! ### L2.3 status — OPEN (tracked in the ledger; Phase-3 scope).

An earlier revision stated L2.3 as the existential "some
`(Bytes, encode, decode)` round-trips" and discharged it with the
identity serialiser (`⟨Term, id, some, fun _ => rfl⟩`). That witness
is vacuous — the existential is satisfied by a "serialiser" that never
produces bytes — so both the statement and its theorem are deleted.

The meaningful L2.3 is `WireRoundTripProperty encode decode` (plus
injectivity of `encode`, the Comparse bar) instantiated at the REAL
CBOR codec: either the Aeneas extraction of
`crates/dlc-protocol/src/wire.rs`, or a Lean-side model proven
equivalent to it. Neither exists yet in Lean; the Rust codec's
round-trip is currently evidenced only by its unit tests. No `Prop`
stand-in belongs here until the encoder does. -/

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
`none` for unsupported trace shapes; this is a real `def` (not
`opaque`), so the §4.4 correspondence is no longer a vacuous statement
over an opaque body.

Current coverage:
  * `[]` → `none` (empty trace has no associated derivation).
  * `[TraceEvent.says P φ]` → `some (Γ, Term.var 0, φ')` where
    `Γ = {additive := [Prop'.says P φ], linear := []}` and
    `φ' = Prop'.says P φ`. The derivation is `Deriv.varA Γ 0 φ' rfl`.
  * Other shapes → `none` (future work: chains, delegations).

The L2.5 statement (`L2_5_TraceLiftingStatement` below) is now stated
over the restricted subset of traces that this implementation
covers, with the singleton-`Says` case as the witness. The full
correspondence (all trace shapes the Tamarin model accepts) is
graduate-thesis-grade work tracked separately. -/
def liftToDeriv : TamarinTrace → Option (Ctx × Term × Prop')
  | [TraceEvent.says P φ] =>
      let Γ : Ctx := { additive := [Prop'.says P φ], linear := [] }
      some (Γ, Term.var 0, Prop'.says P φ)
  | _ => none

/-! ## L2.5 statement.

For every well-formed Tamarin trace, the lifted triple inhabits Deriv. -/

/-- A trace is well-formed if every `DelegateAccept(P, Q, φ)` event has
two strictly-earlier antecedents in the same trace:

  * a `SpeaksForIssued(P, Q)` event (some earlier timestamp), and
  * a `Says(Q, φ)` event (some earlier timestamp).

This is the Lean-side mirror of the Tamarin `non_splicing` lemma —
Tamarin proves the model accepts only well-formed traces, and this
predicate is what `L2_5_TraceLiftingStatement` quantifies over. -/
def TraceWellFormed (t : TamarinTrace) : Prop :=
  ∀ (i : Nat) (P Q : Principal) (φ : Prop'),
    t[i]? = some (TraceEvent.delegateAccept P Q φ) →
      (∃ j : Nat, j < i ∧ t[j]? = some (TraceEvent.speaksForIssued P Q)) ∧
      (∃ k : Nat, k < i ∧ t[k]? = some (TraceEvent.says Q φ))

/-- L2.5 -- Trace-to-derivation lifting statement.

Restricted to the subset of well-formed traces that `liftToDeriv`
currently covers: whenever `liftToDeriv t = some (Γ, M, φ)`, the
triple inhabits `Deriv Γ M φ`. Traces returning `none` (unsupported
shapes) trivially satisfy the implication.

Stronger statements (e.g. "every well-formed trace lifts") require
extending `liftToDeriv` to cover delegations, says-chains, etc. —
tracked as future work in the function's docstring. -/
def L2_5_TraceLiftingStatement : Prop :=
  ∀ (t : TamarinTrace) (Γ : Ctx) (M : Term) (φ : Prop'),
    TraceWellFormed t →
    liftToDeriv t = some (Γ, M, φ) →
    Nonempty (Deriv Γ M φ)

/-- L2.5 -- Proven: every triple `liftToDeriv` produces inhabits Deriv.

For the singleton-`Says` case (the only shape that lifts to `some`):
  * `liftToDeriv [Says P φ] = some ({[Says P φ]}, var 0, Says P φ)`
  * The derivation is `Deriv.varA _ 0 (Prop'.says P φ) rfl`.

All other trace shapes yield `none`, so the implication is vacuous. -/
theorem l2_5_trace_lifting : L2_5_TraceLiftingStatement := by
  intro t Γ M φ _hwf hlift
  -- liftToDeriv only succeeds on `[Says P φ]`; case-split.
  match t, hlift with
  | [TraceEvent.says P φ_t], h =>
      simp [liftToDeriv] at h
      obtain ⟨hΓ, hM, hφ⟩ := h
      subst hΓ
      subst hM
      subst hφ
      exact ⟨Deriv.varA _ 0 (Prop'.says P φ_t) rfl⟩

/-! ## §4.4 status — OPEN (tracked in the ledger; Phase-3 scope).

An earlier revision "composed" L2.5 with the identity-serialiser L2.3
witness into a `protocol_logic_correspondence` theorem. Since the wire
conjunct was vacuous (see the L2.3 note above), the composition proved
nothing beyond `l2_5_trace_lifting`, and it is deleted along with the
`protocol_correspondence_stub : True` alias.

The real §4.4 requires, in order:
1. a total `liftToDeriv` over every trace shape the Tamarin model
   emits, with `TraceWellFormed` load-bearing (today `liftToDeriv`
   covers exactly the singleton `[Says P φ]` shape — see its
   docstring);
2. L2.3 about the real CBOR encoder (round-trip + injectivity);
3. their composition, stated against the executable verifier.

Until those exist, `l2_5_trace_lifting` above is the honest extent of
the protocol-logic correspondence: restricted, and labeled as such. -/

end DLC
