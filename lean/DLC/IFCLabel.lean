/-
DLC — IFC label algebra.

Week-1 carries a placeholder. At M1.Q4.a this module becomes a thin re-export
of nucleus's `PortcullisCore.PermissionLattice`, importing the 165 Lean
theorems that prove the Heyting-algebra laws. No fresh formalization needed.
-/

namespace DLC

/-- An IFC label. Placeholder shape: a sorted-deduped list of capability
indices. M1.Q4.a replaces this with nucleus's 13-dim `PermissionLattice`. -/
structure Label where
  caps : List Nat
  deriving Repr, DecidableEq

namespace Label

/-- `⊥ℓ` — the bottom (least authority) label. -/
def bottom : Label := ⟨[]⟩

end Label

end DLC
