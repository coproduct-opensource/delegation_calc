import DLCD.Rsm
import DLC.IFCLabel
import Mathlib.Logic.Function.Basic

/-! # DLC-D Phase 2.b — the IFC-label half of guarantee 1: log-level noninterference

This module supplies the **confidentiality / information-flow half** of DLC-D's
guarantee 1, complementary to `DLCD.CapSafety` (which supplies the
*authority / integrity-by-construction* half — "only a capability-holder can
commit"). Here we prove the dual property: a **high** committed command
provably does **not leak** into a **low** observer's view of the replicated
store. This is the replicated-state-machine (RSM) analogue of Goguen–Meseguer
noninterference and of FLAQR's replicated-store confidentiality theorem.

## The statement, in one line
The low observer's projection of the converged store is a **function of only
the low-committed subsequence of the log**:

  `view ℓ (applyPrefixL log s0) = view ℓ (applyPrefixL (log.filter (·.label ⊑ ℓ)) s0)`

`log.filter (·.label ⊑ ℓ)` is exactly Goguen–Meseguer's **purge** of the
high commands from the trace; equality of the two low views under purge *is*
noninterference (a low input sequence yields the same low output regardless of
the interleaved high commands). The mechanism that makes it true is the
**no-write-down** discipline of `applyL`: a command labeled `ℓc` writes only its
own cell, so it can never mutate any `ℓ' ⊏ ℓc` cell (Bell–LaPadula
*-property / Denning's lattice flow).

## Prior art (web-searched 2026-07-22; URLs recorded)
- **FLAQR** — Mondal–Algehed–Arden, *Applying consensus and replication
  securely with FLAQR* (CSF 2022): a core calculus for distributed apps with
  heterogeneous quorum replication enforcing END-TO-END IFC; its noninterference
  theorems characterize confidentiality/integrity/availability in the presence
  of consensus, replication, and failures. THE closest prior art — this module
  is the RSM/semantic shadow of FLAQR's replicated-store confidentiality.
  https://arxiv.org/abs/2205.04384 , https://arxiv.org/pdf/2205.04384
  Extended journal version — Mondal–Algehed–Arden, *Flow-limited authorization
  for consensus, replication, and secret sharing*, J. Computer Security 2023:
  https://journals.sagepub.com/doi/abs/10.3233/JCS-230048
- **Goguen–Meseguer noninterference** (1982): the purge/projection framing —
  a low user's outputs are identical whether or not a high user is active; our
  `log.filter (·.label ⊑ ℓ)` is the purge and `view ℓ` is the observation
  function. https://en.wikipedia.org/wiki/Non-interference_(security)
- **Decentralized Label Model (DLM)** — Myers–Liskov, ACM TOSEM 2000
  https://dl.acm.org/doi/10.1145/363516.363526 ; SOSP 1997 *A decentralized
  model for information flow control* https://dl.acm.org/doi/10.1145/268998.266669 .
- **FLAM / FLAC** — Arden et al., *Flow-Limited Authorization* /
  *Distributed Protocols and Heterogeneous Trust*
  https://arxiv.org/pdf/1412.3136 (the label lattice + authority combination
  our reused `CapabilityLattice` order instantiates).
- **seL4 IFC enforcement** — Murray et al., machine-checked information-flow
  enforcement over a deterministic state machine (the closest *verified* RSM-NI
  prior art): https://sel4.systems/Research/pdfs/sel4-from-general-purpose-to-proof-information-flow-enforcement.pdf

## Honest fences (what this IS and IS NOT)
- **Reused lattice, not a fresh one.** The IFC order is DLC's `Label` =
  nucleus's 13-dimensional `CapabilityLattice` (`DLC.IFCLabel`), with `Label.le`
  as `⊑` (`flowsTo`). We ADD `Label.le_refl`/`Label.le_trans` here so the
  "genuine preorder" claim is earned in-file (they rest only on the
  per-component `levelLe` order). The main noninterference theorem consumes
  `Label.le` only as an opaque decidable predicate — it needs neither
  reflexivity nor transitivity, only the projection structure — so the result
  holds for ANY decidable label order; reflexivity/transitivity are proved for
  honesty, not load.
- **This is the RSM / semantic half.** It is noninterference at the
  *replicated-log / store* level. The type-system half — a logical-relations
  (`LRelᴳ`) noninterference over `Deriv`/`CDeriv` derivations, i.e. distributed
  NI carried by the calculus's own typing — is **Phase 2.d, deferred**. This
  file does NOT prove that; it proves the operational store-projection property
  that Phase 2.d's soundness will have to be consistent with.
- **The store is label-indexed** (`LStore := Label → Term`) — the simplest
  faithful model of "an observer at clearance `ℓ` sees only the `⊑ ℓ` cells."
  `view ℓ` returns `Option Term` (`none` = masked/high), so two stores induce
  equal low views iff they agree on every `⊑ ℓ` cell.

## What is proved (the deliverables)
1. `applyL_preserves_below` — a high command (`lc.label ⋢ ℓ`) does not change
   the low view: `view ℓ (applyL lc s) = view ℓ s`.
2. `log_noninterference` — THE theorem above, by induction on the log using (1)
   for the high steps and a low-agreement congruence for the low steps.
   `view_depends_only_on_low` — the convergence corollary: two logs agreeing on
   their `⊑ ℓ` subsequence yield equal low views.
3. `LabelFlowBite.badApplyL_breaks_noninterference` — a `badApplyL` that WRITES DOWN
   (a high command dumps into the ⊥ cell) provably FALSIFIES `log_noninterference`
   on a concrete high command + low observer. The no-write-down discipline is
   load-bearing, not decorative.
4. `LabelFlowWitness.*` — a concrete run with a high AND a low command where the high
   GENUINELY writes (its own cell changes, `≠ s0`) yet the low view is provably
   the low-only run's view. Noninterference is exercised non-vacuously: the high
   command is present and active, it just does not leak.
-/

namespace DLCD

open DLC

/-! ## 0. The label order as an IFC `flowsTo` — reused from `DLC.IFCLabel`.

`⊑` is `DLC.Label.le`, the componentwise order on nucleus's 13-dim
`CapabilityLattice`. We prove it is a genuine preorder (reflexive + transitive)
so the "IFC label order" claim is earned in-file, though the noninterference
theorem below consumes it only as an opaque decidable predicate. -/

open scoped Function

/-- `flowsTo a b` (`a ⊑ b`): information at label `a` may flow to an observer
cleared at `b`. Reused from `DLC.IFCLabel` — the componentwise `CapabilityLattice`
order. Kept as a `Bool` so `view`/`filter` use it directly with no `Decidable`
juggling. -/
abbrev flowsTo (a b : Label) : Bool := Label.le a b

/-- Per-component reflexivity of the 3-point level order. -/
theorem levelLe_refl (a : nucleus_ifc_kernel.CapabilityLevel) :
    Label.levelLe a a = true := by
  cases a <;> rfl

/-- Per-component transitivity of the 3-point level order. -/
theorem levelLe_trans {a b c : nucleus_ifc_kernel.CapabilityLevel}
    (h1 : Label.levelLe a b = true) (h2 : Label.levelLe b c = true) :
    Label.levelLe a c = true := by
  revert h1 h2; cases a <;> cases b <;> cases c <;> decide

/-- `⊑` is reflexive: every label flows to itself. -/
theorem Label.le_refl (a : Label) : Label.le a a = true := by
  simp [Label.le, levelLe_refl]

/-- `⊑` is transitive: information flow composes. Together with `le_refl` this
makes `Label.le` a genuine IFC preorder (the reused nucleus `CapabilityLattice`
order). -/
theorem Label.le_trans {a b c : Label}
    (h1 : Label.le a b = true) (h2 : Label.le b c = true) :
    Label.le a c = true := by
  simp only [Label.le, Bool.and_eq_true, and_assoc] at h1 h2 ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := h2
  exact ⟨levelLe_trans a1 b1, levelLe_trans a2 b2, levelLe_trans a3 b3,
    levelLe_trans a4 b4, levelLe_trans a5 b5, levelLe_trans a6 b6,
    levelLe_trans a7 b7, levelLe_trans a8 b8, levelLe_trans a9 b9,
    levelLe_trans a10 b10, levelLe_trans a11 b11, levelLe_trans a12 b12,
    levelLe_trans a13 b13⟩

/-! ## 1. Labeled commands, the label-indexed store, and the low projection. -/

/-- A labeled command: an RSM `Command` (from `DLCD.Rsm`) plus the IFC `Label`
its write is classified at. This is the `LCommand := Command × Label` of the task
(as a named structure so `.label` reads cleanly in `filter`). -/
structure LCommand where
  /-- The underlying replicated operation. -/
  cmd : Command
  /-- The IFC label this write is classified at. -/
  label : Label

/-- The **label-indexed store**: each IFC label owns a `Term` cell. An observer
cleared at `ℓ` may read exactly the cells `ℓ' ⊑ ℓ`. -/
abbrev LStore := Label → Term

/-- **The low projection.** What an observer cleared at `ℓ` sees: cell `ℓ'` if
`ℓ' ⊑ ℓ`, otherwise `none` (masked — the cell is above the observer's
clearance). Two stores induce equal low views iff they agree on every `⊑ ℓ`
cell. This is Goguen–Meseguer's observation function. -/
def view (ℓ : Label) (s : LStore) : Label → Option Term :=
  fun ℓ' => bif flowsTo ℓ' ℓ then some (s ℓ') else none

/-- Equal low views from cell-agreement below `ℓ` (and conversely on the masked
cells the equality is automatic). The bridge between the extensional `view` and
the pointwise "agree on low cells" reasoning the theorems use. -/
theorem lowAgree_view_eq {ℓ : Label} {s s' : LStore}
    (h : ∀ ℓ', flowsTo ℓ' ℓ = true → s ℓ' = s' ℓ') :
    view ℓ s = view ℓ s' := by
  funext ℓ'
  simp only [view]
  cases hb : flowsTo ℓ' ℓ with
  | false => rfl
  | true => simp only [cond_true]; rw [h ℓ' hb]

/-! ## 2. No-write-down apply. -/

/-- **No-write-down application.** A labeled command writes ONLY its own cell:
`applyL lc s` updates cell `lc.label` to `applyCommand lc.cmd (s lc.label)` and
leaves every other cell untouched. It is a *definitional* guarantee that a
command labeled `ℓc` never mutates any `ℓ' ≠ ℓc` cell — in particular never a
low cell `ℓ' ⊏ ℓc`. (Reading is also confined to the command's own cell, which
is what makes low steps oblivious to high cells — see `applyL_lowAgree`.) -/
def applyL (lc : LCommand) (s : LStore) : LStore :=
  Function.update s lc.label (applyCommand lc.cmd (s lc.label))

/-- A HIGH command (`lc.label ⋢ ℓ`) leaves every low cell exactly as it was:
it writes only cell `lc.label`, and that cell is not `⊑ ℓ`, so no `⊑ ℓ` cell
moves. This is the pointwise core of no-write-down. -/
theorem applyL_high_lowAgree {ℓ : Label} {lc : LCommand} {s : LStore}
    (hhi : flowsTo lc.label ℓ = false) :
    ∀ ℓ', flowsTo ℓ' ℓ = true → applyL lc s ℓ' = s ℓ' := by
  intro ℓ' hlo
  have hne : ℓ' ≠ lc.label := by
    intro heq; rw [heq] at hlo; rw [hlo] at hhi; exact absurd hhi (by decide)
  simp only [applyL, Function.update_of_ne hne]

/-- **THE NO-WRITE-DOWN LEMMA.** A high command does not change the low view.
`view ℓ (applyL lc s) = view ℓ s` whenever `lc.label ⋢ ℓ`. Immediate from
`applyL_high_lowAgree` via `lowAgree_view_eq`. -/
theorem applyL_preserves_below {ℓ : Label} {lc : LCommand} {s : LStore}
    (hhi : flowsTo lc.label ℓ = false) :
    view ℓ (applyL lc s) = view ℓ s :=
  lowAgree_view_eq (applyL_high_lowAgree hhi)

/-- A LOW command (`lc.label ⊑ ℓ`) acts obliviously on the high cells: if two
stores agree on all low cells, they still agree on all low cells after the same
low command. This is what lets the high prefix be discarded — a low command
reads only its own (low) cell, never a high one. -/
theorem applyL_lowAgree {ℓ : Label} {lc : LCommand} {s s' : LStore}
    (hlo : flowsTo lc.label ℓ = true)
    (h : ∀ ℓ', flowsTo ℓ' ℓ = true → s ℓ' = s' ℓ') :
    ∀ ℓ', flowsTo ℓ' ℓ = true → applyL lc s ℓ' = applyL lc s' ℓ' := by
  intro ℓ' hlo'
  by_cases heq : ℓ' = lc.label
  · subst heq
    simp only [applyL, Function.update_self]
    rw [h lc.label hlo]
  · simp only [applyL, Function.update_of_ne heq]
    exact h ℓ' hlo'

/-! ## 3. The committed-log fold and the noninterference theorem. -/

/-- The label-aware analogue of `applyPrefix`: fold `applyL` over a committed
log of labeled commands. This is the converged store as a function of the log. -/
def applyPrefixL (cmds : List LCommand) (s : LStore) : LStore :=
  cmds.foldl (fun st lc => applyL lc st) s

/-- Folding one more command onto a prefix. -/
theorem applyPrefixL_cons (lc : LCommand) (rest : List LCommand) (s : LStore) :
    applyPrefixL (lc :: rest) s = applyPrefixL rest (applyL lc s) := rfl

/-- Congruence for an all-low prefix: if every command in `cmds` is low
(`⊑ ℓ`) and two stores agree on the low cells, they still agree on the low
cells after folding the whole prefix. The engine of the theorem's high case:
the low-committed subsequence is oblivious to what the discarded high prefix
left in the high cells. -/
theorem applyPrefixL_lowAgree {ℓ : Label} : ∀ (cmds : List LCommand),
    (∀ lc ∈ cmds, flowsTo lc.label ℓ = true) → ∀ {s s' : LStore},
    (∀ ℓ', flowsTo ℓ' ℓ = true → s ℓ' = s' ℓ') →
    ∀ ℓ', flowsTo ℓ' ℓ = true → applyPrefixL cmds s ℓ' = applyPrefixL cmds s' ℓ' := by
  intro cmds
  induction cmds with
  | nil => intro _ s s' h ℓ' hlo'; exact h ℓ' hlo'
  | cons lc rest ih =>
    intro hall s s' h ℓ' hlo'
    rw [applyPrefixL_cons, applyPrefixL_cons]
    have hlc : flowsTo lc.label ℓ = true := hall lc List.mem_cons_self
    have hrest : ∀ x ∈ rest, flowsTo x.label ℓ = true :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    exact ih hrest (applyL_lowAgree hlc h) ℓ' hlo'

/-- **THE LOG-LEVEL NONINTERFERENCE THEOREM.** The low observer's projection of
the converged store is a FUNCTION OF ONLY the low-committed subsequence: the
high commands provably do not leak into the low view. `log.filter (·.label ⊑ ℓ)`
is Goguen–Meseguer's purge of the high commands; equality of the two low views
under purge is noninterference.

Proof: induction on the log. A **low** command survives the purge and is applied
on both sides (recurse under it). A **high** command is purged; on the left it
perturbs only high cells (`applyL_high_lowAgree`), and the surviving all-low
subsequence is oblivious to that perturbation (`applyPrefixL_lowAgree`), so the
two low views coincide. -/
theorem log_noninterference (ℓ : Label) (log : List LCommand) (s0 : LStore) :
    view ℓ (applyPrefixL log s0)
      = view ℓ (applyPrefixL (log.filter (fun lc => flowsTo lc.label ℓ)) s0) := by
  induction log generalizing s0 with
  | nil => rfl
  | cons lc rest ih =>
    rw [applyPrefixL_cons]
    by_cases hlc : flowsTo lc.label ℓ = true
    · -- Low command: kept by the purge; recurse under it on both sides.
      have hkeep : (lc :: rest).filter (fun lc => flowsTo lc.label ℓ)
          = lc :: rest.filter (fun lc => flowsTo lc.label ℓ) := by
        simp [hlc]
      rw [hkeep, applyPrefixL_cons]
      exact ih (applyL lc s0)
    · -- High command: purged. It moves only high cells; the low subsequence
      -- is oblivious to that, so the two low views agree.
      have hfalse : flowsTo lc.label ℓ = false := by
        cases hb : flowsTo lc.label ℓ with
        | true => exact absurd hb hlc
        | false => rfl
      have hpurge : (lc :: rest).filter (fun lc => flowsTo lc.label ℓ)
          = rest.filter (fun lc => flowsTo lc.label ℓ) := by
        simp [hfalse]
      rw [hpurge, ih (applyL lc s0)]
      apply lowAgree_view_eq
      apply applyPrefixL_lowAgree
      · intro x hx; exact (List.mem_filter.mp hx).2
      · exact applyL_high_lowAgree hfalse

/-- **Convergence corollary — the low view depends only on the low log.** Two
committed logs that agree on their `⊑ ℓ` subsequence (their Goguen–Meseguer
purge) induce EQUAL low views of the converged store. So a low observer cannot
distinguish two runs by any difference confined to the high commands — the RSM
convergence guarantee, projected to a clearance. -/
theorem view_depends_only_on_low {ℓ : Label} {log₁ log₂ : List LCommand}
    {s0 : LStore}
    (h : log₁.filter (fun lc => flowsTo lc.label ℓ)
        = log₂.filter (fun lc => flowsTo lc.label ℓ)) :
    view ℓ (applyPrefixL log₁ s0) = view ℓ (applyPrefixL log₂ s0) := by
  rw [log_noninterference ℓ log₁, log_noninterference ℓ log₂, h]

/-! ## 4. The right-reason bite — a WRITE-DOWN apply falsifies noninterference.

`badApplyL` dumps every command's result into the ⊥ (lowest) cell, regardless
of the command's own label — a blatant write-down. With it, a HIGH command
mutates the LOW view, and `log_noninterference` provably FAILS. This shows the
no-write-down discipline of `applyL` is doing the real work; noninterference is
not a tautology of the projection shape. -/

namespace LabelFlowBite

/-- The write-down apply: ignores `lc.label` and writes cell `⊥`. A high command
therefore mutates the lowest cell — the archetypal illegal downward flow. -/
def badApplyL (lc : LCommand) (s : LStore) : LStore :=
  Function.update s Label.bottom (applyCommand lc.cmd (s lc.label))

/-- The write-down fold. -/
def badApplyPrefixL (cmds : List LCommand) (s : LStore) : LStore :=
  cmds.foldl (fun st lc => badApplyL lc st) s

/-- A genuinely HIGH label: `read_files := .Always` over the ⊥ base. It does not
flow to ⊥ (`Label.le hi ⊥ = false`), so a command at `hi` is high to the
⊥-observer. -/
def hi : Label := { Label.bottom with read_files := .Always }

/-- The uniform initial store (`var 0` in every cell). -/
def s0 : LStore := fun _ => Term.var 0

/-- A state-CHANGING payload: `λ_. ⟨x, x⟩`, so `applyCommand dup (var 0)`
reduces to `⟨var 0, var 0⟩ ≠ var 0` (reused from `Rsm.RsmAntiVacuity`). -/
def dup : Command := { payload := Term.lam (Prop'.atom 0) (Term.pair (Term.var 0) (Term.var 0)) }

/-- One high command. -/
def hiCmd : LCommand := { cmd := dup, label := hi }

/-- The one-command high log. -/
def log : List LCommand := [hiCmd]

/-- `hi` is genuinely high to the ⊥-observer: it does NOT flow to ⊥. -/
theorem hi_not_low : flowsTo hi Label.bottom = false := rfl

/-- The ⊥-observer's purge of `log` is EMPTY — the high command is dropped. -/
theorem bite_filter : log.filter (fun lc => flowsTo lc.label Label.bottom) = [] := rfl

/-- Under write-down, the ⊥ cell of the full run holds the CHANGED value. -/
theorem bite_lhs_bottom :
    (badApplyPrefixL log s0) Label.bottom = Term.pair (Term.var 0) (Term.var 0) := by
  simp only [badApplyPrefixL, log, List.foldl_cons, List.foldl_nil, badApplyL,
    hiCmd, Function.update_self]
  rfl

/-- The purged (empty) run leaves the ⊥ cell at its initial `var 0`. -/
theorem bite_rhs_bottom :
    (badApplyPrefixL (log.filter (fun lc => flowsTo lc.label Label.bottom)) s0)
      Label.bottom = Term.var 0 := by
  rw [bite_filter]; rfl

/-- **THE BITE.** `log_noninterference` is FALSE for the write-down `badApplyL`:
the ⊥-observer's view of the full run differs from its view of the purged run,
because the high command wrote down into the ⊥ cell. Hence the no-write-down
discipline of `applyL` is load-bearing — remove it and the theorem dies. -/
theorem badApplyL_breaks_noninterference :
    view Label.bottom (badApplyPrefixL log s0)
      ≠ view Label.bottom
          (badApplyPrefixL (log.filter (fun lc => flowsTo lc.label Label.bottom)) s0) := by
  intro hcontra
  have h2 := congrFun hcontra Label.bottom
  simp only [view, flowsTo, Label.le_refl, cond_true] at h2
  rw [bite_lhs_bottom, bite_rhs_bottom] at h2
  exact Term.noConfusion (Option.some.inj h2)

end LabelFlowBite

/-! ## 5. Anti-vacuity witness — a high command PRESENT and ACTIVE, yet not leaking.

A concrete run with BOTH a high and a low command. The high command genuinely
writes (its own cell changes, `≠ s0`), the low command genuinely writes, the two
commands are interleaved and the high one is PRESENT in the log — yet the
⊥-observer's view of the full run equals its view of the low-only (purged) run.
Noninterference is exercised non-vacuously: the high activity is real, it just
does not leak downward. -/

namespace LabelFlowWitness

/-- The observer's clearance: ⊥ (sees only the ⊥ cell). -/
def lo : Label := Label.bottom

/-- A genuinely high label (does not flow to ⊥). -/
def hi : Label := { Label.bottom with read_files := .Always }

/-- The uniform initial store. -/
def s0 : LStore := fun _ => Term.var 0

/-- The state-CHANGING payload `λ_. ⟨x, x⟩`. -/
def dup : Command := { payload := Term.lam (Prop'.atom 0) (Term.pair (Term.var 0) (Term.var 0)) }

/-- A low command (labeled ⊥). -/
def loCmd : LCommand := { cmd := dup, label := lo }

/-- A high command (labeled `hi`). -/
def hiCmd : LCommand := { cmd := dup, label := hi }

/-- The witness log: a high command AND a low command, interleaved. The high
command is genuinely PRESENT (not filtered to nothing on the run side). -/
def wlog : List LCommand := [hiCmd, loCmd]

theorem hi_ne_lo : hi ≠ lo := by decide

theorem lo_ne_hi : lo ≠ hi := by decide

/-- The high command is PRESENT in the committed log. -/
theorem hi_present : hiCmd ∈ wlog := by simp [wlog]

/-- The ⊥-observer's purge keeps ONLY the low command — the high one is dropped,
yet the purge is non-empty (the low run is real, not vacuous). -/
theorem witness_filter : wlog.filter (fun lc => flowsTo lc.label lo) = [loCmd] := rfl

/-- **HIGH IS ACTIVE.** The high command genuinely writes: after the full run
the `hi` cell holds the CHANGED value `⟨var 0, var 0⟩`, distinct from its
initial `s0 hi = var 0`. So noninterference is not discharged over an inert high
command. -/
theorem hi_active :
    (applyPrefixL wlog s0) hi = Term.pair (Term.var 0) (Term.var 0)
      ∧ (applyPrefixL wlog s0) hi ≠ s0 hi := by
  have key : (applyPrefixL wlog s0) hi = Term.pair (Term.var 0) (Term.var 0) := by
    show (applyL loCmd (applyL hiCmd s0)) hi = _
    simp only [applyL, loCmd, hiCmd, Function.update_of_ne hi_ne_lo, Function.update_self]
    rfl
  refine ⟨key, ?_⟩
  rw [key]; exact fun h => Term.noConfusion h

/-- The low command is also active: the ⊥ cell of the full run holds the changed
value — so the surviving low subsequence is doing real work too. -/
theorem lo_active :
    (applyPrefixL wlog s0) lo = Term.pair (Term.var 0) (Term.var 0) := by
  show (applyL loCmd (applyL hiCmd s0)) lo = _
  simp only [applyL, loCmd, hiCmd, Function.update_self, Function.update_of_ne lo_ne_hi]
  rfl

/-- **THE NON-VACUITY PAYOFF.** Despite the active high command, the ⊥-observer's
view of the full run equals its view of the low-only (purged) run — the high
command does not leak. Instance of `log_noninterference`; combined with
`hi_active`/`hi_present`/`witness_filter` this is a genuinely non-vacuous
exercise of noninterference (high present, high active, high excluded from the
low run, low views nonetheless equal). -/
theorem low_view_unchanged :
    view lo (applyPrefixL wlog s0)
      = view lo (applyPrefixL (wlog.filter (fun lc => flowsTo lc.label lo)) s0) :=
  log_noninterference lo wlog s0

/-- Spelled against the concrete purged log `[loCmd]`: the ⊥-observer sees
exactly the low-only run, with the high command gone. -/
theorem low_view_is_low_only :
    view lo (applyPrefixL wlog s0) = view lo (applyPrefixL [loCmd] s0) := by
  rw [low_view_unchanged, witness_filter]

end LabelFlowWitness

end DLCD
