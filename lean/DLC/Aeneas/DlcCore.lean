/-
Aeneas-generated translation of `crates/dlc-core` — re-export module.

The sub-files in `lean/DLC/Aeneas/DlcCore/` are generated verbatim by
`charon cargo --preset aeneas` + `aeneas -backend lean -split-files`.
They are NOT hand-edited; CI (`Aeneas Rust → Lean drift`, gated by
`coproduct-opensource/aeneas-ci`) regenerates and diffs against
committed content on every PR. Drift is a soundness break: T1 would
otherwise prove a Lean function no longer corresponding to the Rust.

Bootstrap landed at M1.Q1.d via PR #57 (workflow wiring) + the
follow-up `proof-aeneas-bootstrap` PR (this commit).

To regenerate locally:
  bash scripts/aeneas-translate.sh
-/

-- Short module names (`DlcCore.*`) resolve against this lib's
-- `srcDir := "DLC/Aeneas"` (see lakefile.lean, lean_lib «DLCAeneas», whose
-- root is `DlcCore`), matching the imports Aeneas emits inside Funs.lean /
-- Types.lean.
import DlcCore.Types
import DlcCore.Funs
-- Import the HAND-FILLED external models (renamed from FunsExternal_Template
-- per Aeneas `-split-files`), NOT the template: the template's `axiom`s and
-- this file's `def`s share names and must not both be elaborated. The
-- template stays on disk purely as the drift-gate regeneration reference.
import DlcCore.FunsExternal
