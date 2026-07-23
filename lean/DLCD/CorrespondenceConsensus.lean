import DlcDRsm            -- the consensus layer: dlc_d_rsm.consensus.{is_quorum, decided}

/-! # DLC-D Phase R2.2b — the consensus correspondence squares.

Companion to `DLCD.Correspondence` (the transition-core module). The two
generated trees `DlcCore` and `DlcDRsm` cannot be imported into the same Lean
module (a `@[discriminant isize]` instance-name collision on the two `Term`
copies), so the `dlc_d_rsm.consensus` squares live here.

These squares carry **no** `AppCommandRefines` hypothesis — consensus counting
does not route through the reducer. They relate the generated boolean
quorum/decision engine to the *operational* majority predicate (`2·card > n`);
the `Finset`-cardinality `Prop` form (`DLCD.IsQuorum`, `DLCD.Decided`) stays
Lean-only (parent §1.2). -/

namespace DLCD.CorrespondenceConsensus

open Aeneas Aeneas.Std Result
open dlc_d_rsm

/-! ## `is_quorum_square` (NO `hcmd`; bool ↔ majority). -/

/-- **`is_quorum_square`.** The generated `consensus.is_quorum card n` decides the
operational strict-majority predicate `2·card > n`, provided the doubling
`2·card` does not overflow `U32` (the honest `U32` fence for the multiply). -/
theorem is_quorum_square (card n : Std.U32) (hno : 2 * card.val < 2 ^ 32) :
    consensus.is_quorum card n = ok (decide (n.val < 2 * card.val)) := by
  simp only [consensus.is_quorum]
  have heq := UScalar.mul_equiv 2#u32 card
  rw [show (2#u32 * card) = UScalar.mul 2#u32 card from rfl]
  cases hm : UScalar.mul 2#u32 card with
  | ok z =>
    rw [hm] at heq
    obtain ⟨_, hz, _⟩ := heq
    have hzv : z.val = 2 * card.val := by simpa using hz
    simp only [bind_tc_ok]
    congr 1
    rw [decide_eq_decide]
    simp only [GT.gt]
    scalar_tac
  | fail e =>
    exfalso; rw [hm] at heq; simp only [UScalar.max] at heq; scalar_tac
  | div => rw [hm] at heq; exact heq.elim

end DLCD.CorrespondenceConsensus
