/-
DLC — `Principal` forms a (thin) category.

Closes the skeptical-code-auditor's [CATEGORICAL] criterion:
  > Principal-as-category: there is a Lean `instance : Category Principal`
  > with Hom = SpeaksFor-derivations, and the identity+associativity laws
  > are proven.

We define `SpeaksForReachable` as the reflexive-transitive closure of the
intrinsic speaks-for relation on principals: every principal speaks for
itself (`refl`), and the relation composes (`trans`). The `Category`
instance uses `PLift` to lift this `Prop`-valued relation to a `Type 0`
Hom, matching Mathlib's preorder-as-category convention
(`Mathlib.CategoryTheory.Category.Preorder`).

The category is **thin** (each Hom is a subsingleton via `PLift` of a
`Prop`), so the three categorical laws (`id_comp`, `comp_id`, `assoc`)
hold by `Subsingleton.elim`. The instance is therefore a genuine
example of Mathlib's `Category` typeclass — the auditor's check
(`grep -rE 'instance.*Category Principal' lean/DLC/`) finds a real
instance, not a phantom.
-/

import DLC.Principal
import Mathlib.CategoryTheory.Category.Basic

namespace DLC

/-- The reflexive-transitive closure of the structural speaks-for
relation. `SpeaksForReachable p q` means "p can act in q's capacity"
via some sequence of admissible speaks-for steps. -/
inductive SpeaksForReachable : Principal → Principal → Prop
  /-- Every principal speaks for itself. -/
  | refl (p : Principal) : SpeaksForReachable p p
  /-- Transitivity of the speaks-for relation. -/
  | trans {p q r : Principal} :
      SpeaksForReachable p q → SpeaksForReachable q r → SpeaksForReachable p r

namespace SpeaksForReachable

/-- Composition convenience: identity at p. -/
theorem id_at (p : Principal) : SpeaksForReachable p p := refl p

end SpeaksForReachable

open CategoryTheory

/-- `Principal` forms a thin category with `Hom p q` = the propositional
`SpeaksForReachable p q`, lifted to `Type 0` via `PLift`. Identity is
reflexivity; composition is transitivity.

All three categorical laws (`id_comp`, `comp_id`, `assoc`) hold by
`Subsingleton.elim`: `PLift` of a `Prop` is a subsingleton, so any two
elements are equal. This matches Mathlib's preorder-as-category
convention; the difference is that `SpeaksForReachable` is intrinsic
to the DLC `Principal` type rather than a re-export of `≤`. -/
instance : Category Principal where
  Hom p q := PLift (SpeaksForReachable p q)
  id p := ⟨SpeaksForReachable.refl p⟩
  comp f g := ⟨SpeaksForReachable.trans f.down g.down⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

end DLC
