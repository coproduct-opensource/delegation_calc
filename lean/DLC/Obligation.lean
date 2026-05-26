/-
DLC — Linear obligations.

Production realization mirrors nucleus's `DischargedBundle` sealed-constructor
pattern. The linear structure is what makes T4 (obligation soundness) sound.
-/

import DLC.Principal
import DLC.Time

namespace DLC

/-- An action identifier; opaque outside the runtime's obligation table. -/
structure ActionId where
  bytes : List UInt8
  deriving Repr, DecidableEq

/-- An obligation expression. -/
inductive Obligation : Type where
  | top  : Obligation
  | bot  : Obligation
  | actOf : Principal → ActionId → Obligation
  | within : TimeBound → Obligation
  | tensor : Obligation → Obligation → Obligation
  | lolli : Obligation → Obligation → Obligation
  deriving Repr, DecidableEq

end DLC
