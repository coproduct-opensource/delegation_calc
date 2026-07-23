import DLCD.DistributedNI
import DLCD.CapSafety
import DLC.Progress

/-! # DLC-D Phase 2.h — CLOSING THE DISTRIBUTED-NI TYPED-LOG FENCE

`DLCD.DistributedNI` (Phase 2.d) closes the LOW-command case of distributed
noninterference *under a hypothesis* — `worldStep_preserves_low` and
`deliver_preserves_low` take a raw assumption

```
htyped : ∀ (n) (c : Command), L[n]? = some c →
  Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true
```

("every committed command's payload is a closed *core* `φ ⊸ φ` store-endomorphism").
2.d flags this as residual: it *assumes* a typed-log invariant rather than
establishing it. This module CLOSES that fence by making the invariant a
**theorem established at the commit gate**, exactly mirroring how
`DLCD.CapSafety`'s `WellFormedLog` makes "every committed command is authorized"
an enforce-by-construction consequence instead of an assumption.

## The move — admission control + Wright–Felleisen preservation

We add a typed-commit ADMISSION GATE: a `WellTypedLog φ` is an inductive
provenance predicate (like `WellFormedLog`) whose ONLY growth rule
(`commitTyped`) demands a `WellTypedCmd φ c` proof as a required field. So a
well-typed log can only be built by supplying the typing proof at each commit.
`wellTypedLog_implies_htyped` then EXTRACTS 2.d's `htyped` from that provenance
by induction — this is the syntactic-type-soundness **preservation** shape
("well-typed commands preserve well-formed logs, by induction on the typing
derivation"; Wright–Felleisen / Harper): the typed-log property is an invariant
of every reachable committed log, because the only constructor that extends the
log re-establishes it. `worldStep_preserves_low_typed` then reaches 2.d's
low-case conclusion with `WellTypedLog φ g₁.log` in place of the raw `htyped`.

`WellTypedLog` is **non-circular**: it is NOT "every element is well-typed"
(that is the theorem `wellTypedLog_implies_htyped`); it is "was built only by
typed commits", from which per-element typing is derived — the same provenance /
extraction discipline as `WellFormedLog` → `capability_safety`.

## Prior art (web-searched 2026-07-22; URLs recorded)
- **Wright–Felleisen**, *A Syntactic Approach to Type Soundness* (Info. & Comp.
  1994): progress + PRESERVATION (subject reduction) — "a program remains
  well-typed as it executes", proved by induction on the typing derivation. The
  typed-log invariant here is the log-level preservation statement.
  https://people.irisa.fr/David.Cachera/Enseignement/ASM/peignier.pdf
  CMU 17-363 notes (preservation of a well-formed log by induction on the typing
  derivation): https://www.cs.cmu.edu/~aldrich/courses/17-363/notes/lecture10-soundness.pdf
- **Timany–Krebbers–Dreyer–Birkedal**, *A Logical Approach to Type Soundness*
  (JACM 2024): the Iris logical-relations reformulation of preservation-style
  soundness. https://iris-project.org/pdfs/2024-jacm-logical-type-soundness.pdf
- **Schultz et al.**, *Formal Verification of a Distributed Dynamic
  Reconfiguration Protocol* (MongoDB Raft): invariant preservation across ALL
  reachable states of a replicated state machine — the SMR analogue of "the typed
  invariant holds for every committed log a `worldStep` can reach."
  https://arxiv.org/pdf/2109.11987
- **Bauer**, *Proof-Carrying Authorization* (the admission-gate pattern this
  mirrors, via `DLCD.CapSafety`): the monitor admits only what carries the
  required proof. http://users.ece.cmu.edu/~lbauer/papers/thesis.pdf

## Honest fences (what this closes and what it does NOT)
- **CLOSED:** 2.d's `htyped` is now a commit-gate invariant, not a raw
  assumption. `worldStep_preserves_low_typed` needs only `WellTypedLog φ g₁.log`
  (enforced by construction), the closed-store hypotheses, and `LowEquivG`.
- **STILL OPEN (unchanged from 2.d; do NOT read this as closing them):**
  (1) store-type CHANGE across a command (a command mapping type φ to a distinct
  ψ) is still not modeled — `WellTypedCmd`/`LowEquivG` are at a fixed store type;
  (2) the live-log / `FailureBudget` fair-delivery SCHEDULING closure is still
  Phase-1.0-oracular — we close a single `worldStep` under the typed-log gate and
  iterate it purely. This module ADDS a composing layer; it does not modify or
  weaken any theorem in `DistributedNI.lean` or `CapSafety.lean`.

## What is proved (deliverables)
1. `WellTypedCmd φ c` — the typed-command obligation (closed core `φ ⊸ φ`).
2. `WellTypedLog φ` — the typed-log ADMISSION GATE (inductive provenance;
   `commitTyped` carries the `WellTypedCmd` proof), + `commitTypedLog` (the
   proof-required commit function).
3. `wellTypedLog_implies_htyped` — EXACTLY 2.d's `htyped`, now a THEOREM (the
   preservation extraction by induction on `WellTypedLog`).
4. `worldStep_preserves_low_typed` — 2.d's `worldStep_preserves_low` conclusion
   with `WellTypedLog φ g₁.log` replacing the raw `htyped`.
5. `Bite.*` — an untyped command (`CoreTerm = false`, a frozen `verify`) is
   REJECTED: `¬ WellTypedCmd φ badCmd`, hence `¬ WellTypedLog φ [badCmd]`.
6. `Witness.*` — a REAL identity endomorphism admitted via `commitTyped`, and
   `worldStep_preserves_low_typed` closing the fence on a concrete 2-replica
   config with NO raw `htyped` assumption.
-/

namespace DLCD

open DLC

/-! ## 1. The typed-command obligation.

A command is well-typed at store type `φ` when its payload is a closed *core*
`PropDeriv` endomorphism `φ ⊸ φ` — precisely the per-command load-bearing
hypothesis `DistributedNI.applyCommand_preserves_LRel` consumes. (`Prop'.imp` is
DLC's function arrow; `applyCommand` applies the payload to the store, so a
`φ → φ` payload is a store-type-preserving transformer.) -/

/-- **Typed-command obligation.** `c`'s payload is a closed core `φ ⊸ φ`
store-endomorphism: a `PropDeriv [] payload (φ ⊸ φ)` exists and the payload is a
`CoreTerm` (no frozen `verify`/`declassify`/`boxed`/`attenuate`/`discharge`). -/
def WellTypedCmd (φ : Prop') (c : Command) : Prop :=
  Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true

/-! ## 2. The typed-log invariant, established by an ADMISSION GATE.

`WellTypedLog φ` mirrors `DLCD.CapSafety.WellFormedLog`: an inductive PROVENANCE
predicate, NOT "every element is well-typed". The empty log is well-typed; the
ONLY way to grow it is `commitTyped`, which demands a `WellTypedCmd φ c` proof as
a required field. So a well-typed log can only be assembled by supplying the
typing proof at each commit — admission control at the type level. -/

/-- **Provenance of a typed committed log.** The empty log is well-typed;
extending a well-typed log by a `WellTypedCmd`-carrying command keeps it
well-typed. The `WellTypedCmd` proof is a field of `commitTyped` — the sole
growth rule — so this predicate captures "was built only by typed commits."
Non-circular: it does NOT say "every element is well-typed" (that is
`wellTypedLog_implies_htyped`). -/
inductive WellTypedLog (φ : Prop') : CommittedLog → Prop where
  /-- The empty log — no commits yet — is trivially well-typed. -/
  | nil : WellTypedLog φ []
  /-- Extending a well-typed log by a well-typed command keeps it well-typed.
  The `WellTypedCmd` proof is a required argument of the constructor. -/
  | commitTyped {log : CommittedLog} {c : Command}
      (h : WellTypedLog φ log) (ht : WellTypedCmd φ c) :
      WellTypedLog φ (log ++ [c])

/-- **The proof-required typed commit.** Append `c` to a well-typed log — but
ONLY with an in-hand proof `ht : WellTypedCmd φ c`. The result is packaged with
its `WellTypedLog` provenance, so the ONLY way into a typed log is through a
typed command. This is the admission gate as a function (cf.
`DLCD.CapSafety.commit`). -/
def commitTypedLog {φ : Prop'} (log : CommittedLog) (c : Command)
    (ht : WellTypedCmd φ c) (hwt : WellTypedLog φ log) :
    {log' : CommittedLog // WellTypedLog φ log'} :=
  ⟨log ++ [c], WellTypedLog.commitTyped hwt ht⟩

/-! ## 3. DERIVING `htyped` — the preservation extraction.

The typed-log property holds of EVERY committed command in a well-typed log —
Wright–Felleisen preservation at the log level, extracted by induction on the
`WellTypedLog` provenance (mirror of `CapSafety.capability_safety`). -/

/-- Every command in a well-typed log satisfies the typed-command obligation.
Induction on the provenance: the empty log has no commands; a `commitTyped` node
either extends an already-typed log (IH) or contributes exactly the command
whose `WellTypedCmd` proof it carried. This EXTRACTS per-element typing; it does
not re-assert the definition. -/
theorem wellTypedLog_forall_mem {φ : Prop'} {log : CommittedLog}
    (hwt : WellTypedLog φ log) : ∀ c ∈ log, WellTypedCmd φ c := by
  induction hwt with
  | nil => intro c hc; exact absurd hc List.not_mem_nil
  | @commitTyped log c' h ht ih =>
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc; subst hc; exact ht

/-- **THE DELIVERABLE — 2.d's `htyped`, now a THEOREM.** Every committed command
in a well-typed log is a closed core `φ ⊸ φ` store-endomorphism. This is
character-for-character the hypothesis `DistributedNI.worldStep_preserves_low` /
`deliver_preserves_low` assumed — established here by the commit gate rather than
assumed. Proof: `WellTypedCmd` is definitionally the conjunction, extracted per
element via `wellTypedLog_forall_mem` after `log[n]? = some c ⇒ c ∈ log`. -/
theorem wellTypedLog_implies_htyped {φ : Prop'} {log : CommittedLog}
    (hwt : WellTypedLog φ log) :
    ∀ (n : Nat) (c : Command), log[n]? = some c →
      Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true := by
  intro n c hn
  exact wellTypedLog_forall_mem hwt c (List.mem_of_getElem? hn)

/-! ## 4. CLOSING THE FENCE IN 2.d.

The same conclusion as `DistributedNI.worldStep_preserves_low`, with the raw
`htyped` assumption replaced by the enforced-by-construction `WellTypedLog`
invariant — fed through `wellTypedLog_implies_htyped`. -/

/-- **LOW-COMMAND PRESERVATION, FENCE CLOSED.** A `worldStep` delivering a shared
committed log to two closed, low-equivalent configs preserves `LowEquivG` —
where the log's typing is an ADMISSION-GATE invariant (`WellTypedLog φ g₁.log`),
not a raw assumption. Body: feed `wellTypedLog_implies_htyped hwt` into
`DistributedNI.worldStep_preserves_low`. -/
theorem worldStep_preserves_low_typed (ℓLow : Label) (φ : Prop')
    {g₁ g₂ : GlobalConfig} (hlog : g₁.log = g₂.log)
    (hwt : WellTypedLog φ g₁.log)
    (hc₁ : ∀ r ∈ g₁.replicas, Closed r.store)
    (hc₂ : ∀ r ∈ g₂.replicas, Closed r.store)
    (hrel : LowEquivG ℓLow φ g₁ g₂) :
    LowEquivG ℓLow φ (worldStep g₁) (worldStep g₂) :=
  worldStep_preserves_low ℓLow φ hlog (wellTypedLog_implies_htyped hwt) hc₁ hc₂ hrel

/-! ## 5. THE RIGHT-REASON BITE — an untyped command is rejected.

An UNTYPED command — payload with `CoreTerm = false` (a frozen `verify`, exactly
the says-elimination form the core excludes) — cannot satisfy `WellTypedCmd`, so
it cannot be admitted via `commitTyped`. `wellTypedLog_implies_htyped` therefore
FAILS for any hand-built log containing it: that list is NOT `WellTypedLog`. The
typing gate is real, not decorative (cf. `CapSafety.unauth_not_authorized`). -/

namespace Bite

/-- A frozen `verify` payload: `CoreTerm (Term.verify …) = false`, so it is
outside the core the low case needs (it is the says-elimination the endomorphism
discipline excludes). -/
def badCmd : Command :=
  { payload := Term.verify (Principal.atom ⟨[0]⟩) (Term.var 0) ⟨0, []⟩ }

/-- **THE BITE.** `badCmd` is NOT well-typed at any `φ`: its payload's
`CoreTerm` is `false`, contradicting the second conjunct of `WellTypedCmd`. So
no typing proof for it can be supplied at a `commitTyped`. -/
theorem badCmd_untyped (φ : Prop') : ¬ WellTypedCmd φ badCmd := by
  rintro ⟨_, hcore⟩
  simp [badCmd, CoreTerm] at hcore

/-- **THE BITE, at the log level.** A log holding `badCmd` cannot be
`WellTypedLog`: if it were, `wellTypedLog_implies_htyped` would extract a
`WellTypedCmd φ badCmd` at index `0`, contradicting `badCmd_untyped`. The
admission gate genuinely refuses the untyped command. -/
theorem badLog_not_wellTyped (φ : Prop') : ¬ WellTypedLog φ [badCmd] := by
  intro hwt
  exact badCmd_untyped φ (wellTypedLog_implies_htyped hwt 0 badCmd rfl)

end Bite

/-! ## 6. ANTI-VACUITY WITNESS — a REAL typed command admitted, the fence closed.

A genuine identity endomorphism `λx:φ'. x : φ' ⊸ φ'` (`CoreTerm = true`), with a
hand-built `PropDeriv`, admitted to a `WellTypedLog` via `commitTyped`; then
`worldStep_preserves_low_typed` applied to a concrete 2-replica config carrying
that typed log — with NO raw `htyped` assumption anywhere. Non-vacuous: the
`PropDeriv` is inhabited by an explicit derivation, and the fence closes on a
concrete run. -/

namespace WitnessTyped

/-- The (low, observable) store type. -/
def φ' : Prop' := Prop'.atom 0

/-- The identity endomorphism command `λx:φ'. x`. -/
def idCmd : Command := { payload := Term.lam φ' (Term.var 0) }

/-- **The real typing derivation.** `impI` over the additive-`var` leaf builds
`PropDeriv [] (λx:φ'. x) (φ' ⊸ φ')` — an explicit, non-opaque derivation of the
identity endomorphism at the store type. -/
def idDeriv : PropDeriv [] (Term.lam φ' (Term.var 0)) (Prop'.imp φ' φ') :=
  .impI [] φ' φ' (Term.var 0) (.varA [φ'] 0 φ' rfl)

/-- `idCmd` is well-typed: the real derivation, and `CoreTerm (λx. x) = true`. -/
theorem idCmd_wellTyped : WellTypedCmd φ' idCmd :=
  ⟨⟨idDeriv⟩, rfl⟩

/-- **A well-typed log built through the admission gate.** `[idCmd]` (`= [] ++
[idCmd]`) is `WellTypedLog φ'` ONLY because `idCmd_wellTyped` is supplied to
`commitTyped`. -/
theorem log_wellTyped : WellTypedLog φ' [idCmd] :=
  WellTypedLog.commitTyped WellTypedLog.nil idCmd_wellTyped

/-- ...and equivalently via the proof-required commit FUNCTION. -/
def typedLog : {log' : CommittedLog // WellTypedLog φ' log'} :=
  commitTypedLog [] idCmd idCmd_wellTyped WellTypedLog.nil

/-- A concrete closed store — the identity lambda (closed above 0). -/
def store : Term := Term.lam (Prop'.atom 0) (Term.var 0)

theorem store_closed : Closed store := by
  unfold Closed store
  exact closedAbove_lam_iff.mpr (closedAbove_var_iff.mpr (by omega))

/-- A concrete 2-replica config carrying the typed log `[idCmd]`. -/
def w : GlobalConfig :=
  { replicas := [⟨0, store, 0⟩, ⟨1, store, 0⟩], log := [idCmd],
    budget := FailureBudget.zero 1 }

/-- The store obligation at the low type `φ'` is `Joinable store store`, trivial
by reflexivity. -/
theorem lrel_store_refl (ℓLow : Label) : LRel ℓLow φ' store store := by
  simp only [φ', LRel]
  exact ⟨store, .refl _, .refl _⟩

/-- The two runs (identical here — a low-typed store must agree between runs)
are `LowEquivG` at the low store type. -/
theorem lowEquiv : LowEquivG Label.bottom φ' w w := by
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · exact ⟨rfl, rfl, lrel_store_refl _⟩
  · exact ⟨rfl, rfl, lrel_store_refl _⟩

/-- Every replica store in `w` is closed. -/
theorem w_closed : ∀ r ∈ w.replicas, Closed r.store := by
  intro r hr
  simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact store_closed

/-- **THE FENCE CLOSED ON A CONCRETE RUN.** `worldStep_preserves_low_typed`
delivers the typed log `[idCmd]` to the two closed low-equivalent replicas and
preserves `LowEquivG` — using `log_wellTyped` (the admission-gate invariant) and
NO raw `htyped` assumption. The typed-log fence of 2.d is closed here on a
genuinely-active world step with a real typed command. -/
theorem lowEquiv_preserved :
    LowEquivG Label.bottom φ' (worldStep w) (worldStep w) :=
  worldStep_preserves_low_typed Label.bottom φ' rfl log_wellTyped w_closed w_closed lowEquiv

end WitnessTyped

end DLCD
