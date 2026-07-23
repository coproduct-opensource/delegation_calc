/-
Aeneas-generated translation of `crates/dlc-d-rsm` — re-export module.

The sub-files in `lean/DLCD/Aeneas/DlcDRsm/` are generated verbatim by
`charon cargo --preset aeneas` (run in `crates/dlc-d-rsm`, whose `.llbc`
serializes to the cargo workspace root as `dlc_d_rsm.llbc`) + `aeneas
-backend lean -split-files`. `dlc-d-rsm` path-depends on `dlc-core`, so the
single `dlc_d_rsm.llbc` INLINES the `dlc_core.*` items: this tree is
self-contained (it carries its own copy of the `dlc_core.syntax.Term`
translation under the `dlc_d_rsm` namespace).

They are NOT hand-edited; CI (`Aeneas Rust → Lean drift`, gated by
`scripts/check-drift.sh`) regenerates and diffs against committed content on
every PR as the SECOND Charon target, alongside `dlc-core` →
`lean/DLC/Aeneas/DlcCore`. Drift is a soundness break: the R2 transport
theorem (R2.2–R2.4) would otherwise refine a Lean function no longer
corresponding to the Rust runtime core.

R2.1 ships ONLY this translated artifact + the drift gate — NO correspondence
proof. The refinement `Rust world_step ≡ Lean worldStep` and the transport of
G1–G4 through it are R2.2–R2.4.

To regenerate locally:
  bash scripts/aeneas-translate.sh
-/

-- Short module names (`DlcDRsm.*`) resolve against this lib's
-- `srcDir := "DLCD/Aeneas"` (see lakefile.lean, lean_lib «DLCDRsmAeneas», whose
-- root is `DlcDRsm`), matching the imports Aeneas emits inside Funs.lean /
-- Types.lean.
import DlcDRsm.Types
import DlcDRsm.Funs
-- Import the HAND-FILLED external models (renamed from FunsExternal_Template
-- per Aeneas `-split-files`), NOT the template: the template's `axiom` and
-- this file's `def` share the name `dlc_core.rsm.Command.Insts`
-- `.CoreCmpPartialEqCommand.eq` and must not both be elaborated. The template
-- stays on disk purely as the drift-gate regeneration reference.
import DlcDRsm.FunsExternal
