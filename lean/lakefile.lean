import Lake
open Lake DSL

package «dlc» where
  -- Release mode for native-decide heavy proofs (T1, T4).
  buildType := .release
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    -- Generous heartbeat budget; individual lemmas can still override.
    ⟨`maxHeartbeats, (400000 : Nat)⟩
  ]

-- Aeneas standard library. Pinned to the same commit nucleus uses so the
-- Charon-emitted .llbc files in this workspace match `nucleus`'s output.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "ad905f518523fd8553dfbd089feb438ffa5c04ae" / "backends" / "lean"

-- Re-export the verified IFC label algebra from nucleus's portcullis-core.
-- DLC's IFC labels ARE nucleus's CapabilityLattice; no fresh formalization.
--
-- The relative path requires nucleus to be checked out as a sibling clone.
-- CI (.github/workflows/lean.yml) does this via a parallel checkout step.
require portcullisCore from "../../nucleus/crates/portcullis-core/lean"

-- Mathlib for HeytingAlgebra, Multiset (linear context), Order theory, and the
-- categorical infrastructure used by T3 / the strong indexed monad.
-- MUST be declared LAST: `portcullisCore` transitively requires mathlib at an
-- older rev, and Lake lets the last `require mathlib` win so Mathlib's own
-- transitive dep versions (aesop/batteries/Qq/…) take precedence and
-- `lake exe cache get` computes the correct hashes.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

-- DLC core library — syntax, judgments, reduction, substitution.
lean_lib «DLC» where
  roots := #[
    `DLC.Syntax,
    `DLC.Judgment,
    `DLC.Principal,
    `DLC.IFCLabel,
    `DLC.Obligation,
    `DLC.Time,
    `DLC.Subst,
    `DLC.Reduce,
    `DLC.ReduceMeta,
    `DLC.Graded,
    `DLC.IndexedMonad
  ]

-- The four headline theorems live in dedicated libs so `lake build` can run
-- each one in parallel and the ledger.sh script can report per-theorem status.

lean_lib «Decidability» where
  roots := #[`DLC.Decidability]

-- L1 (linear-lever campaign): the `CtxWellFormed` disambiguation invariant
-- and its equivalence to the shipped checker. Depends on Judgment + Decidability.
lean_lib «CtxWellFormed» where
  roots := #[`DLC.CtxWellFormed]

-- L3a boxI prerequisite: every derivable term is closed above its context
-- size. Representation-independent; fed to boxI's fixed-context obligation.
lean_lib «DerivClosed» where
  roots := #[`DLC.DerivClosed]

-- CARVe resource-vector context foundation for the L3/L4 migration
-- (spec/carve-context-design-2026-07.md). Generic; the judgment migration
-- instantiates the entry type at Prop'. Standalone, imports nothing from DLC.
lean_lib «CarveCtx» where
  roots := #[`DLC.CarveCtx]

-- CARVe-migrated judgment (DLC-D Phase 0, increment 1): the real Term/Prop'
-- fragment over resource-vector contexts + weakening-in-the-middle
-- (cderiv_shift), lifting CarveProto onto the real types. The L3-shaped
-- keystone of the linear-lever migration; substitution (L4) mirrors Wood-Atkey.
lean_lib «CarveJudgment» where
  roots := #[`DLC.CarveJudgment]

-- Validation prototype for the CARVe context migration
-- (spec/carve-context-design-2026-07.md). Self-contained: imports nothing
-- from DLC, so it can be judged on its own. CI type-checks it because an
-- unchecked validation artifact rots.
lean_lib «CarveProto» where
  roots := #[`CarveProto]

-- DLC-D Phase 1.0: the RSM operational substrate — FailureBudget contract,
-- Command/Replica/CommittedLog/GlobalConfig, deterministic applyCommand, and
-- the convergence seed (two replicas over the same committed prefix agree).
-- New module tree `lean/DLCD/`; the committed log is an oracle (consensus is
-- a later increment).
lean_lib «DLCD» where
  roots := #[`DLCD.Rsm, `DLCD.FaultGrade, `DLCD.CapSafety, `DLCD.CapSafetyLinear, `DLCD.Consensus, `DLCD.ByzantineConsensus, `DLCD.MultiDecree, `DLCD.MultiDecreeLiveness, `DLCD.Liveness, `DLCD.Termination, `DLCD.Linearizable, `DLCD.Witness, `DLCD.LabelFlow, `DLCD.Calm, `DLCD.DistributedNI, `DLCD.TypedLog, `DLCD.Summary]

lean_lib «Correspondence» where
  roots := #[`DLC.Correspondence]

-- DLC-D Phase R2.2b: the decode ⟦·⟧ and the conditional structural refinement
-- squares relating the Aeneas-generated dlc-core / dlc-d-rsm functions to
-- DLCD.Rsm, assuming the reducer correspondence (AppCommandRefines) as a stated
-- hypothesis (R2.3 discharges it), plus the closed anti-vacuity witness.
-- Imports DLCD (hand model) + the generated DlcCore/DlcDRsm trees, so building
-- this lib COMPILES those trees in the main build (previously drift-gated only).
-- Name differs from the existing «Correspondence» (the T2 crypto one).
lean_lib «DLCDCorrespondence» where
  roots := #[`DLCD.Correspondence, `DLCD.CorrespondenceConsensus]

-- DLC-D Phase R2.4a: the TRANSPORT capstone. Spends the R2.3 partial-correctness
-- squares (DLCD.Correspondence) to pull the hand guarantees (G1-cap, G2, G4, G1-NI)
-- back to the deployed Rust runtime as `rust_*` corollaries conditioned on the Rust
-- op returning `ok`. Single generated tree (dlc_core only, via DLCD.Correspondence);
-- does NOT import DLCD.CorrespondenceConsensus (the dlc_d_rsm tree would collide).
lean_lib «DLCDTransport» where
  roots := #[`DLCD.Transport]

lean_lib «NonInterference» where
  roots := #[`DLC.NonInterference, `DLC.NonInterferenceTwoRun, `DLC.NonInterferenceLR, `DLC.NonInterferenceEnv, `DLC.NonInterferenceFundamental]

-- Rung 3b-0: progress for the closed computational core (T3 prerequisite).
lean_lib «Progress» where
  roots := #[`DLC.Progress]

lean_lib «ObligationSoundness» where
  roots := #[`DLC.ObligationSoundness]

-- §4.4 — protocol-logic correspondence theorem (Phase 2 closure).
lean_lib «ProtocolCorrespondence» where
  roots := #[`DLC.ProtocolCorrespondence]

-- Witness files: non-vacuity and audit regressions. A headline theorem's
-- ledger status may not report `proven*` unless its companion witness
-- builds (see scripts/ledger.sh). AxiomAudit machine-checks the 2026-07
-- finding that the legacy T2 axiom was refutable in-system.
lean_lib «Witness» where
  roots := #[`DLC.Witness.AxiomAudit, `DLC.Witness.T1, `DLC.Witness.T3,
             `DLC.Witness.L1, `DLC.Witness.T4]

-- Aeneas-generated translation of crates/dlc-core. Regenerated by
-- scripts/aeneas-translate.sh; non-clean diffs block merge.
-- Root is the SHORT name `DlcCore` (not `DLC.Aeneas.DlcCore`): with
-- `srcDir := "DLC/Aeneas"` the module `DlcCore` maps to `DLC/Aeneas/DlcCore.lean`
-- and the sub-modules `DlcCore.Types/.Funs/.FunsExternal` to
-- `DLC/Aeneas/DlcCore/*.lean` — matching the short imports Aeneas emits inside
-- the generated tree. (The former `DLC.Aeneas.DlcCore` root doubled the srcDir
-- prefix to `DLC/Aeneas/DLC/Aeneas/DlcCore.lean` and never resolved, which is
-- why this lib had only ever been drift-gated, never compiled.)
lean_lib «DLCAeneas» where
  roots := #[`DlcCore]
  srcDir := "DLC/Aeneas"

-- Aeneas-generated translation of crates/dlc-d-rsm (DLC-D Phase R2.1). The
-- verified-runtime-core mirror of `DLCD.Rsm`; the single `dlc_d_rsm.llbc`
-- inlines `dlc_core`, so this is a self-contained tree. Regenerated by
-- scripts/aeneas-translate.sh as the SECOND Charon target; non-clean diffs
-- block merge. Like DLCAeneas, EXCLUDED from the per-lib CI build and gated
-- solely by scripts/check-drift.sh (R2.1 ships no correspondence proof).
-- Root is the SHORT name `DlcDRsm` (see the DLCAeneas note above): with
-- `srcDir := "DLCD/Aeneas"` it maps to `DLCD/Aeneas/DlcDRsm.lean` and the
-- sub-modules `DlcDRsm.Types/.Funs/.FunsExternal` to `DLCD/Aeneas/DlcDRsm/*`.
lean_lib «DLCDRsmAeneas» where
  roots := #[`DlcDRsm]
  srcDir := "DLCD/Aeneas"

-- CT-unification proof #1: coproduct-algebra ↔ Mathlib lattice bridge.
-- One kernel proof; both live adopters (remediation-hvc::MaturityRank,
-- trust-atlas::Maturity) inherit the Mathlib order library.
lean_lib «CoproductAlgebra» where
  roots := #[`DLC.CoproductAlgebra]

-- CT-unification proof #3 (moonshot): the graded natural transformation
-- τ : Graded⟨RiskGrade⟩ ⇒ Graded⟨DpBudget⟩ (risk join-grade → DP additive-grade).
lean_lib «GradedBridge» where
  roots := #[`DLC.GradedBridge]

-- M3 capstone: the graded mixed distributive law λ : D∘T ⇒ T∘D + ambient-budget-aware
-- DP admission. Completes the τ-bridge object; content rests on GradedBridge's lax law.
lean_lib «GradedDistributiveLaw» where
  roots := #[`DLC.GradedDistributiveLaw]

-- M2: the bridge generalized — any lax monoid hom into DpBudget induces the coherences;
-- the risk↔DP bridge is one instance.
lean_lib «GradedBridgeGeneric» where
  roots := #[`DLC.GradedBridgeGeneric]
