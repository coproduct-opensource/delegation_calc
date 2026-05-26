/-
T2 — Cryptographic correspondence.

The keystone theorem:

  ∀ Γ M φ K, (Deriv Γ M φ) ↔ (DerivCrypto Γ K M φ)

where `DerivCrypto` is the keyring-threading judgment that checks every
signature at every `says` node. Lands at M2.M15 (Phase-2 closure), depending
on L2.3 (wire ↔ symbolic encoding) and L2.4 (EasyCrypt computational bridge).

The `Ed25519_EUF_CMA` axiom appears in `#print axioms t2_correspondence`; the
EasyCrypt bridge discharges it computationally.
-/

import DLC.Judgment

namespace DLC

/-- Placeholder. T2 lands at M2.M15. -/
theorem t2_correspondence_stub : True := trivial

end DLC
