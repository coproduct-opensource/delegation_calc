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

import DLC.Aeneas.DlcCore.Types
import DLC.Aeneas.DlcCore.Funs
import DLC.Aeneas.DlcCore.FunsExternal_Template
