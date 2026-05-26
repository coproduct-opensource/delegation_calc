/-
DLC — Principals.

Principal composition operators: ∧ (conjunctive), ∨ (disjunctive), ⊓ (acting-as,
associative but NOT commutative). The `k(p)` form from the spec is `keyId`.
-/

namespace DLC

/-- Stable identifier for an atomic principal. Production realization: a
truncated SHA-256 of the SPIFFE-ID (32 bytes). -/
structure PrincipalId where
  bytes : List UInt8
  deriving Repr, DecidableEq

/-- A principal expression. -/
inductive Principal : Type where
  | atom : PrincipalId → Principal
  | and  : Principal → Principal → Principal
  | or   : Principal → Principal → Principal
  /-- `acting p q` = "p acting in q's capacity" (associative, NOT commutative). -/
  | acting : Principal → Principal → Principal
  deriving Repr, DecidableEq

/-- A keyring entry: principal → public-key bytes. -/
structure KeyRecord where
  principal  : PrincipalId
  alg        : UInt8
  publicKey  : List UInt8
  deriving Repr, DecidableEq

end DLC
