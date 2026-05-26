/-
Re-export of nucleus's verified IFC algebra into the `DLC.IFC` namespace.

This module is the bridge between DLC's abstract `IFCLabel` and nucleus's
concrete 13-dimensional `CapabilityLattice`. The strategic choice (per the
Phase-1 plan): DLC's IFC label algebra **is** nucleus's lattice — no fresh
formalization, the 165 Lean theorems already discharged by nucleus's
`portcullis-core/lean/` are imported wholesale.

Re-exports:
  * `CapabilityLevel` (3-valued: Never / LowRisk / Always) as `DLC.IFC.Level`.
  * `CapabilityLattice` (13-tuple of `CapabilityLevel`) as `DLC.IFC.LabelImpl`.
  * The `HeytingAlgebra` instance from `PortcullisCoreBridge`.

The DLC-facing API (`DLC.IFCLabel`) keeps a thin abstraction over this so
the calculus's typing rules don't need to know about the 13-component
structure — they speak only the lattice ops `bottom`, `join`, `meet`, `le`.
-/

import PortcullisCore.Types

namespace DLC.IFC

/-- DLC's IFC capability levels. Identically nucleus's `CapabilityLevel`. -/
abbrev Level := portcullis_core.CapabilityLevel

/-- DLC's concrete IFC label — nucleus's 13-dimensional capability lattice. -/
abbrev LabelImpl := portcullis_core.CapabilityLattice

end DLC.IFC
