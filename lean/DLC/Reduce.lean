/-
DLC — Small-step reduction.

Subject reduction (M1.Q2.c) is the headline result here. Once proven, T4 and
T3 both depend on it.
-/

import DLC.Syntax

namespace DLC

/-- One step of reduction. `none` denotes a normal form. -/
def step (_t : Term) : Option Term := none

end DLC
