/-
DLC — Time bounds for the `◇_τ` modality.

The verifier checks anchor commitments (drand round, NIST beacon pulse) at the
realization layer (`dlc-crypto::time_anchor`). The calculus here knows only the
abstract `TimeBound`.
-/

namespace DLC

/-- A time bound: milliseconds since UNIX epoch. -/
structure TimeBound where
  epochMs : Nat
  deriving Repr, DecidableEq

end DLC
