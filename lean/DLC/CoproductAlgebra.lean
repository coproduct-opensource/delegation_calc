/-
DLC — coproduct-algebra ↔ Mathlib lattice bridge.

CT-unification proof #1 (the highest-fan-out one). The Rust crate
`coproduct-algebra` defines a `Lattice` trait that three repos adopt
(portcullis-core, `remediation-hvc::MaturityRank`, `trust-atlas::Maturity`),
each re-checking the laws at RUNTIME via `verify_lattice_laws`. This file gives
the KERNEL backing:

  1. A `CLattice` / `LawfulCLattice` class mirroring the Rust trait.
  2. The observation that both live adopters are the SAME 6-element chain
     `Rank6` (their rank *labels* differ — Declared/Stated, RecomputeChecked/
     ParityPinned — but the *order* is identical), so one Lean model covers both.
  3. `Rank6` is proven a `LawfulCLattice` by `decide` — kernel-checked law
     witnesses replacing the Rust runtime `verify_lattice_laws`.
  4. A `LinearOrder` for `Rank6` (it is a total order), from which Mathlib hands
     it the entire `Order.*` / `Lattice` / `DistribLattice` library FREE; and a
     `decide`-proof that the trait's `meet`/`join` ARE Mathlib's `⊓`/`⊔` (= min/max).

Net: one proof, every adopter inherits ~the whole order library, and the
"weakest-link" min-merge is now a kernel-checked lattice meet rather than an
ad-hoc `.min()`.

Model-level: the Lean `Rank6` models the Rust ranks; a structural-parity test on
the Rust side (the enum discriminants are 0..5) keeps them in lockstep. No Aeneas
needed — these are tiny finite lattices, which sidesteps the stale
`CapabilityLattice` extraction blocker entirely.

Mirrors `coproduct-algebra/src/lib.rs`.
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

namespace DLC.CoproductAlgebra

/-! ## The trait, mirrored -/

/-- Lean mirror of the Rust `coproduct_algebra::Lattice` trait: meet/join/leq. -/
class CLattice (α : Type*) where
  cmeet : α → α → α
  cjoin : α → α → α
  cleq : α → α → Prop

/-- The laws the Rust `verify_lattice_laws` checks at runtime — here as a class
so they are discharged once, in the kernel, per type. -/
class LawfulCLattice (α : Type*) extends CLattice α where
  meet_comm : ∀ a b : α, cmeet a b = cmeet b a
  join_comm : ∀ a b : α, cjoin a b = cjoin b a
  meet_assoc : ∀ a b c : α, cmeet (cmeet a b) c = cmeet a (cmeet b c)
  join_assoc : ∀ a b c : α, cjoin (cjoin a b) c = cjoin a (cjoin b c)
  meet_idem : ∀ a : α, cmeet a a = a
  join_idem : ∀ a : α, cjoin a a = a
  meet_absorb : ∀ a b : α, cmeet a (cjoin a b) = a
  join_absorb : ∀ a b : α, cjoin a (cmeet a b) = a
  leq_iff_meet : ∀ a b : α, cleq a b ↔ cmeet a b = a

/-! ## The shared 6-element chain that BOTH adopters realize

`remediation-hvc::MaturityRank` and `trust-atlas::Maturity` are both 0..5 total
orders; as lattices they are the *same* object. Modelling that object once is
itself a small unification (one type, two Rust adopters). -/

/-- The canonical 6-rank chain. `r0 < r1 < … < r5`. -/
inductive Rank6 where
  | r0 | r1 | r2 | r3 | r4 | r5
  deriving DecidableEq, Repr, Fintype

namespace Rank6

/-- Forgetful map to `Fin 6` — the order-reflecting injection. -/
def toFin : Rank6 → Fin 6
  | r0 => 0 | r1 => 1 | r2 => 2 | r3 => 3 | r4 => 4 | r5 => 5

theorem toFin_injective : Function.Injective toFin := by decide

/-- Meet = min on the chain. -/
def meet : Rank6 → Rank6 → Rank6 := fun a b => if a.toFin ≤ b.toFin then a else b
/-- Join = max on the chain. -/
def join : Rank6 → Rank6 → Rank6 := fun a b => if a.toFin ≤ b.toFin then b else a
/-- Order = the chain order. -/
def leq : Rank6 → Rank6 → Prop := fun a b => a.toFin ≤ b.toFin

instance : CLattice Rank6 where
  cmeet := meet
  cjoin := join
  cleq := leq

end Rank6

/-- **The law witness.** `Rank6` satisfies every lattice law — proven by `decide`
over the finite carrier. This is the Rust `verify_lattice_laws` made kernel-checked,
and it discharges *both* adopters at once (they are this same chain). -/
instance : LawfulCLattice Rank6 where
  meet_comm := by decide
  join_comm := by decide
  meet_assoc := by decide
  join_assoc := by decide
  meet_idem := by decide
  join_idem := by decide
  meet_absorb := by decide
  join_absorb := by decide
  -- `cleq` is a `Prop`-valued instance projection, so `decide` can't synthesize a
  -- `Decidable` instance through it. Case-split, then unfold to concrete `Fin` facts that
  -- `simp` discharges.
  leq_iff_meet := by
    intro a b
    cases a <;> cases b <;>
      simp [CLattice.cleq, CLattice.cmeet, Rank6.leq, Rank6.meet, Rank6.toFin]

/-! ## Mathlib inheritance via the linear order

`Rank6` is a total order, so a single `LinearOrder` instance hands it Mathlib's
entire lattice hierarchy (`Lattice`, `DistribLattice`, `BoundedOrder`, …). We then
show the trait's `cmeet`/`cjoin` coincide with Mathlib's `⊓`/`⊔`, so any adopter
that conforms to the trait inherits the whole order library through this bridge. -/

/-- Pull the linear order back from `Fin 6` along the order-reflecting injection.
Stable Mathlib API (`LinearOrder.lift'`), avoiding version-fragile constructors. -/
instance : LinearOrder Rank6 := LinearOrder.lift' Rank6.toFin Rank6.toFin_injective

/-- The trait meet is exactly Mathlib's lattice meet (= `min`). -/
theorem cmeet_eq_inf (a b : Rank6) : CLattice.cmeet a b = a ⊓ b := by
  cases a <;> cases b <;> decide

/-- The trait join is exactly Mathlib's lattice join (= `max`). -/
theorem cjoin_eq_sup (a b : Rank6) : CLattice.cjoin a b = a ⊔ b := by
  cases a <;> cases b <;> decide

/-- The trait order agrees with Mathlib's `≤`. -/
theorem cleq_iff_le (a b : Rank6) : CLattice.cleq a b ↔ a ≤ b := by
  constructor <;> intro h <;> exact h

/-! ## Weakest-link merge = the lattice meet-fold

The Rust `min_merge` (= `meet_all(..).unwrap_or(bottom)`) over a chain is the
lattice meet-fold. We state the binary core that the fold iterates; the
`unwrap_or(bottom)` empty-case is the deliberate conservative choice documented
in `coproduct-algebra` (⊥, not the lattice ⊤ identity). -/

/-- Folding meet over a list, conservative empty = ⊥ (`r0`). Mirrors
`MaturityRank::min_merge` / `trust-atlas` `meet_all(..).unwrap_or(bottom)`. -/
def minMerge : List Rank6 → Rank6
  | [] => Rank6.r0
  | x :: xs => xs.foldl (· ⊓ ·) x

/-- Weakest-link: the merge never exceeds any member (for non-empty input the
result is ≤ the head). A small, kernel-checked sanity theorem the runtime
`verify_lattice_laws` cannot give. -/
theorem minMerge_le_head (x : Rank6) (xs : List Rank6) :
    minMerge (x :: xs) ≤ x := by
  simp only [minMerge]
  induction xs generalizing x with
  | nil => exact le_refl x
  | cons y ys ih =>
      -- `foldl f x (y :: ys) = foldl f (x ⊓ y) ys` holds definitionally.
      have step : (y :: ys).foldl (· ⊓ ·) x = ys.foldl (· ⊓ ·) (x ⊓ y) := rfl
      rw [step]
      exact le_trans (ih (x ⊓ y)) inf_le_left

end DLC.CoproductAlgebra
