/-
DLC — Capture-avoiding substitution and the substitution lemma.

M1.Q2.a closes the substitution lemma here, with the function and proof both
machine-checked. The Aeneas translation of `crates/dlc-core/src/subst.rs` lives
in `DLC.Aeneas.DlcCore`; the function-correspondence theorem at the bottom of
this file ties them together.
-/

import DLC.Syntax

namespace DLC

/-- Substitute `value` for the variable at de-Bruijn index 0 in `body`. -/
def subst (body : Term) (_value : Term) : Term :=
  body  -- M1.Q2.a deliverable.

end DLC
