/-
DLC — IFC label algebra.

M1.Q4.a re-exports nucleus's 13-dim `CapabilityLattice` from
`PortcullisCoreImport`. The DLC-facing `Label` type is an alias for the
nucleus type, which means the 165 Lean theorems on the lattice (HeytingAlgebra,
GaloisConnection, lattice laws) apply directly without re-proving.

The propositional ops we need at the calculus surface — `bottom`, `join`,
`meet`, `le` — are exposed through the alias so DLC's `Prop'.at` and the
`app-IFC` rule (which takes the join of labels) bind to the right targets.
-/

-- Direct import of nucleus's Aeneas-generated capability types. The 165
-- nucleus Lean theorems on this lattice (HeytingAlgebra, GaloisConnection,
-- declassification proofs) apply to DLC's `Label` wholesale through this
-- alias — no fresh formalization.
import PortcullisCore.Types

namespace DLC

/-- A DLC IFC label. Aliased to nucleus's `CapabilityLattice` (13-dim).
M1.Q4.a established this binding. -/
abbrev Label := portcullis_core.CapabilityLattice

namespace Label

/-- `⊥ℓ` — the bottom (least authority) label.

A 13-tuple of `.Never`s. Nucleus's `CapabilityLevel` is a linear order with
`.Never < .LowRisk < .Always`. -/
def bottom : Label :=
  { read_files  := .Never
  , write_files := .Never
  , edit_files  := .Never
  , run_bash    := .Never
  , glob_search := .Never
  , grep_search := .Never
  , web_search  := .Never
  , web_fetch   := .Never
  , git_commit  := .Never
  , git_push    := .Never
  , create_pr   := .Never
  , manage_pods := .Never
  , spawn_agent := .Never
  }

/-- Componentwise max — the lattice join. The `app-IFC` rule produces
labels of this shape: `ℓ₁ ⊔ ℓ₂` for an application's result label. -/
def join (a b : Label) : Label :=
  { read_files  := max a.read_files  b.read_files
  , write_files := max a.write_files b.write_files
  , edit_files  := max a.edit_files  b.edit_files
  , run_bash    := max a.run_bash    b.run_bash
  , glob_search := max a.glob_search b.glob_search
  , grep_search := max a.grep_search b.grep_search
  , web_search  := max a.web_search  b.web_search
  , web_fetch   := max a.web_fetch   b.web_fetch
  , git_commit  := max a.git_commit  b.git_commit
  , git_push    := max a.git_push    b.git_push
  , create_pr   := max a.create_pr   b.create_pr
  , manage_pods := max a.manage_pods b.manage_pods
  , spawn_agent := max a.spawn_agent b.spawn_agent
  }

end Label

end DLC
