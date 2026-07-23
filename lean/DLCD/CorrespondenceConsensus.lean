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

open Aeneas Aeneas.Std Result ControlFlow
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

/-! ## `decided_square` (NO `hcmd`; `countP` loop induction).

The generated `consensus.decided` counts the votes equal to `v` (via the faithful
structural `Command` `==`) and calls `is_quorum` on that count against the vote
total. It decodes to the operational strict-majority predicate over
`List.countP (· == some v)`. The count is proven equal to `countP` by an
accumulator induction over the `decided_loop`; the quorum step reuses
`is_quorum_square`. The `Command` equality is the DlcDRsm tree's real
`ok (c₁ == c₂)` (not an axiom), so the count is decode-faithful by construction. -/

-- Generic loop plumbing (duplicated: the `DlcCore`/`DlcDRsm` trees cannot
-- co-import, so `DLCD.Correspondence`'s copies are not visible here).
private theorem loopK_cont {α β} (F : α → Result (ControlFlow α β)) (x x' : α)
    (h : F x = ok (ControlFlow.cont x')) : loop F x = loop F x' := by rw [loop.eq_1, h]

private theorem loopK_fin {α β} (F : α → Result (ControlFlow α β)) (x : α) (y : β)
    (h : F x = ok (ControlFlow.done y)) : loop F x = ok y := by rw [loop.eq_1, h]

private theorem nextK_succ {a b : Std.Usize} (hlt : a.val < b.val)
    (hsucc : a.val + 1 ≤ Std.Usize.max) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := a, «end» := b }
      = ok (some a, { start := UScalar.ofNatCore (a.val + 1) (by scalar_tac), «end» := b }) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, lift, bind_ok, bind_tc_ok]
  rw [if_pos (by simp [hlt]), core.iter.range.UScalarStep.forward_checked, dif_pos (by scalar_tac)]
  rfl

private theorem nextK_done {a b : Std.Usize} (hge : b.val ≤ a.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := a, «end» := b }
      = ok (none, { start := a, «end» := b }) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, lift, bind_ok, bind_tc_ok]
  rw [if_neg (by simp; omega)]

/-- The vote-counting loop equals `List.countP (· == some v)` over the remaining
votes, offset by the accumulator. Induction on the remaining count. -/
private theorem decided_loop_spec
    (votes : Slice (Option dlc_core.rsm.Command)) (v : dlc_core.rsm.Command)
    (n : Std.Usize) (hn : n.val = votes.val.length) :
    ∀ (rem : Nat) (k : Std.Usize) (count0 : Std.U32),
      n.val = k.val + rem → k.val ≤ n.val →
      count0.val + (votes.val.drop k.val).countP (fun o => o == some v) ≤ Std.U32.max →
      ∃ cnt : Std.U32,
        consensus.decided_loop { start := k, «end» := n } votes v count0 = ok cnt
          ∧ cnt.val = count0.val + (votes.val.drop k.val).countP (fun o => o == some v) := by
  intro rem
  induction rem with
  | zero =>
    intro k count0 hrem hkn hfence
    have hke : k.val = n.val := by omega
    have hde : votes.val.drop k.val = [] := by rw [hke, hn]; exact List.drop_length
    have hbody : consensus.decided_loop.body votes v { start := k, «end» := n } count0
        = ok (ControlFlow.done count0) := by
      unfold consensus.decided_loop.body
      rw [nextK_done (a := k) (b := n) (by omega)]
      simp
    refine ⟨count0, ?_, ?_⟩
    · rw [show consensus.decided_loop { start := k, «end» := n } votes v count0
            = loop (fun p => consensus.decided_loop.body votes v p.1 p.2)
                ({ start := k, «end» := n }, count0) from rfl,
          loopK_fin _ _ count0 hbody]
    · rw [hde]; simp
  | succ m ih =>
    intro k count0 hrem hkn hfence
    have hk_lt : k.val < n.val := by omega
    have hk_len : k.val < votes.val.length := by rw [← hn]; exact hk_lt
    have hle := Slice.length_ineq votes
    have hsucc : k.val + 1 ≤ Std.Usize.max := by omega
    set k1 : Std.Usize := UScalar.ofNatCore (k.val + 1) (by scalar_tac) with hk1_def
    have hk1v : k1.val = k.val + 1 := by rw [hk1_def]; exact UScalar.ofNatCore_val_eq _
    have hdrop : votes.val.drop k.val
        = (votes.val[k.val]'hk_len) :: votes.val.drop k1.val := by
      rw [hk1v]; exact List.drop_eq_getElem_cons hk_len
    -- `incr` = whether vote k counts toward v.
    have hcountP_cons :
        (votes.val.drop k.val).countP (fun o => o == some v)
          = (if (votes.val[k.val]'hk_len == some v) then 1 else 0)
            + (votes.val.drop k1.val).countP (fun o => o == some v) := by
      rw [hdrop, List.countP_cons]; ring
    -- Reduce the loop body to `cont` with the incremented count.
    obtain ⟨cnt1, hbody, hcnt1v⟩ :
        ∃ cnt1 : Std.U32,
          consensus.decided_loop.body votes v { start := k, «end» := n } count0
            = ok (ControlFlow.cont ({ start := k1, «end» := n }, cnt1))
          ∧ cnt1.val = count0.val + (if (votes.val[k.val]'hk_len == some v) then 1 else 0) := by
      cases hvk : votes.val[k.val]'hk_len with
      | none =>
        refine ⟨count0, ?_, by simp [hvk]⟩
        unfold consensus.decided_loop.body
        rw [nextK_succ hk_lt hsucc]
        simp [Slice.index_usize, List.getElem?_eq_getElem hk_len, hvk, hk1_def]
      | some c =>
        by_cases hc : (c == v) = true
        · have hincr : count0.val + 1 ≤ Std.U32.max := by
            have h1 : 1 ≤ (votes.val.drop k.val).countP (fun o => o == some v) := by
              rw [hdrop]; simp [List.countP_cons, hvk, hc]
            omega
          obtain ⟨cnt1, hadd, hcnt1v⟩ :=
            WP.spec_imp_exists (U32.add_spec (x := count0) (y := 1#u32) (by scalar_tac))
          refine ⟨cnt1, ?_, ?_⟩
          · unfold consensus.decided_loop.body
            rw [nextK_succ hk_lt hsucc]
            simp [Slice.index_usize, List.getElem?_eq_getElem hk_len, hvk,
              dlc_core.rsm.Command.Insts.CoreCmpPartialEqCommand.eq, hc, hadd, hk1_def]
          · rw [hcnt1v]; simp [hvk, hc]
        · refine ⟨count0, ?_, ?_⟩
          · unfold consensus.decided_loop.body
            rw [nextK_succ hk_lt hsucc]
            simp [Slice.index_usize, List.getElem?_eq_getElem hk_len, hvk,
              dlc_core.rsm.Command.Insts.CoreCmpPartialEqCommand.eq, hc, hk1_def]
          · have hcf : (c == v) = false := by simpa using hc
            simp [hvk, hcf]
    obtain ⟨cnt, hloop, hcntv⟩ := ih k1 cnt1 (by omega) (by omega)
      (by rw [hcnt1v]; rw [hcountP_cons] at hfence; omega)
    refine ⟨cnt, ?_, ?_⟩
    · rw [show consensus.decided_loop { start := k, «end» := n } votes v count0
            = loop (fun p => consensus.decided_loop.body votes v p.1 p.2)
                ({ start := k, «end» := n }, count0) from rfl,
          loopK_cont _ _ ({ start := k1, «end» := n }, cnt1) hbody,
          show loop (fun p => consensus.decided_loop.body votes v p.1 p.2)
                ({ start := k1, «end» := n }, cnt1)
            = consensus.decided_loop { start := k1, «end» := n } votes v cnt1 from rfl,
          hloop]
    · rw [hcntv, hcnt1v, hcountP_cons]; ring

/-- **`decided_square`.** The generated `consensus.decided` decides the operational
strict-majority predicate over the count of votes equal to `v`. Fences: the vote
total and twice the matching count fit `U32` (honest, benign). -/
theorem decided_square (votes : Slice (Option dlc_core.rsm.Command))
    (v : dlc_core.rsm.Command) (hlen : votes.val.length < 2 ^ 32)
    (hquorum : 2 * (votes.val.countP (fun o => o == some v)) < 2 ^ 32) :
    consensus.decided votes v
      = ok (decide (votes.val.length < 2 * (votes.val.countP (fun o => o == some v)))) := by
  have hn : (Slice.len votes).val = votes.val.length := Slice.len_val _
  have hle := Slice.length_ineq votes
  have hcple := List.countP_le_length (l := votes.val) (p := fun o => o == some v)
  have h0u : ((0#usize : Std.Usize)).val = 0 := rfl
  have h0v : ((0#u32 : Std.U32)).val = 0 := rfl
  have hlU : votes.val.length ≤ Std.U32.max := by scalar_tac
  obtain ⟨cnt, hloop, hcntv⟩ := decided_loop_spec votes v (Slice.len votes) hn
    (Slice.len votes).val 0#usize 0#u32 (by rw [h0u]; omega) (by rw [h0u]; omega)
    (by rw [h0u, h0v, List.drop_zero]; omega)
  have hi2 : (UScalar.cast .U32 (Slice.len votes)).val = votes.val.length := by
    simp only [UScalar.cast_val_eq]; rw [hn]; apply Nat.mod_eq_of_lt; omega
  have hdec : consensus.decided votes v
      = consensus.is_quorum cnt (UScalar.cast .U32 (Slice.len votes)) := by
    show (do let count ← consensus.decided_loop { start := 0#usize, «end» := Slice.len votes }
                          votes v 0#u32
             consensus.is_quorum count (UScalar.cast .U32 (Slice.len votes)))
         = consensus.is_quorum cnt (UScalar.cast .U32 (Slice.len votes))
    rw [hloop, bind_tc_ok]
  rw [hdec, is_quorum_square cnt (UScalar.cast .U32 (Slice.len votes))
    (by rw [hcntv]; simpa using hquorum), hi2, hcntv]
  simp

end DLCD.CorrespondenceConsensus
