# Phase 4 — BFT liveness / view-change (design)

Status: **design-first.** This is the last of the plan's three named Phase-4 gaps (revocation and
multi-hop attenuation are closed). Liveness is a genuinely hard area and this document does NOT claim a
proof — it fixes the target and recommends the *provable* form. Scrupulous honesty about what is and is
not established is the whole point.

## 0. What already EXISTS (so the gap is stated precisely, not over-claimed)

DLC-D's consensus layer is **safety-complete and honestly liveness-fenced today**:

- **Byzantine SAFETY, transported.** `rust_byz_agreement` / `rust_consensus_agreement`
  (`lean/DLCD/TransportConsensus.lean`): the deployed `consensus.decided`/`byz_decided` engine cannot
  certify two different values on one ballot — quorum intersection, realized on the executable Rust.
  `n ≥ 3f+1`, `2f+1` quorums (`ByzantineConsensus.lean`).
- **Per-step delivery PROGRESS, transported.** `DLCD.Transport.rust_deliver_correct` (via
  `deliver_square`): one delivery step of the deployed engine advances the decoded replica exactly as
  the hand `deliver`; `command_eventually_applied` (single-replica, needs NO fairness) rides on it.
- **Model-level fair-scheduling LIVENESS.** `Liveness.command_eventually_written`,
  `MultiDecreeLiveness.fair_quorum_decides` — a command is eventually written *under a
  `FailureBudget.fairDelivery` hypothesis*. This is honestly **model-level** (TransportConsensus.lean
  §R2.4b): `fairDelivery = true` is an **assumption on the run**, not a property any `rsm` op computes,
  so there is no transition to route a runtime square through.
- **Replica CONVERGENCE, transported.** `rust_replicas_converge` (two replicas folding the same
  committed prefix decode to equal stores).

The existing code already **names** the missing piece (`ByzantineConsensus.lean:84`,
`MultiDecree.lean:44`): Byzantine liveness via view-change / leader-election / partial-synchrony, and
that leader election is deferred (Paxos/BFT *safety* holds regardless of leader — a dueling-proposer
scenario can stall progress but never break agreement). This document consolidates that deferral into a
concrete target.

## 1. The gap — precisely

Two things are absent:

1. **No view / leader / round in the machine.** `dlc-core::rsm` (`Command`, `Replica`, `GlobalConfig`,
   `world_step`, `commit`) has **no view number, no leader, no view-change transition**. `CommittedLog`
   is an *oracle* ("real single-decree consensus that fills each slot is a later increment"). So a
   crashed or Byzantine **leader** has no *replacement mechanism* — nothing rotates the proposer.
2. **Fair delivery is ASSUMED, not DERIVED.** The model-level liveness takes `fairDelivery` as a
   hypothesis. A real BFT-liveness result would *derive* eventual progress from a **leader-rotation +
   eventual-synchrony** assumption (a faulty leader is timed out and replaced until a correct leader
   proposes during a synchronous period), rather than assuming fair delivery outright.

## 2. Why liveness needs an assumption (FLP / partial synchrony)

This is not a defect to be proved away — it is a theorem of the field, and the design must state it:

- **FLP (Fischer–Lynch–Paterson 1985):** no deterministic protocol solves consensus in an *asynchronous*
  network with even one crash fault while guaranteeing termination. So **safety can be unconditional,
  but liveness cannot** — it requires an extra assumption. https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf
- **Partial synchrony (Dwork–Lynch–Stockmeyer 1988):** liveness is recoverable under a **Global
  Stabilization Time (GST)** — after some unknown GST the network is synchronous (bounded message
  delay). BFT protocols (PBFT, HotStuff, Jolteon) guarantee progress *after GST*, via **view-change**:
  timers advance the view until a correct leader proposes during a synchronous window.
  https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf

The honest liveness statement is therefore **conditional**: *under `< (n/3)` Byzantine faults AND
partial synchrony (a GST after which delays are bounded), every correct proposal is eventually committed*
— once the rotating view lands on a correct leader after GST.

## 3. The DLC-D formalization target — a view-change protocol over the RSM

Extend the *model* (not `dlc-core` — see fence) with the missing structure:

- **View / round.** A `view : Nat` and a `leader(view) = view mod n` rotation.
- **View-change transition.** A replica that does not see progress within a timeout broadcasts a
  view-change; `2f+1` view-change messages form a **view-change certificate** that advances the view and
  installs the next leader (PBFT `NEW-VIEW`, or HotStuff's linear `QC`-carrying view-change). Reuse the
  existing **quorum-certificate machinery** (`verify_qc` / the `2f+1`-of-`3f+1` quorum already proved for
  safety) for the view-change certificate — the same intersection argument that gives agreement gives
  *view-change safety* (no two correct leaders commit conflicting values in one slot).
- **The liveness lemma (target):** `after GST, if the current leader is correct and ≥ 2f+1 correct
  replicas are synchronous, a decision is reached within `O(1)` views` — i.e. the view sequence
  eventually stabilizes on a correct leader and that leader drives a commit. Progress = a decreasing
  measure on "views until a correct synchronous leader".

## 4. The honest recommendation — a BOUNDED, model-checked liveness

**A full Lean liveness proof is out of scope for this toolchain, and saying so plainly is the honest
call.** Safety is an *inductive invariant* (`∀` over reachable states) — exactly what this no-Mathlib
Lean corpus proves well, and why `rust_byz_agreement` exists. Liveness is a *temporal* property
(`◇ decided` — eventually), needing fairness hypotheses and well-founded / temporal-logic reasoning
(TLA's `WF`/`SF`, or a Löb/step-indexed liveness framework) that this toolchain does **not** have and
that would be a multi-month infrastructure build to add.

The pragmatic **provable** target is a **bounded, model-checked** liveness, matching how the field
actually mechanizes it:

- **TLA+/TLC** — specify the view-change protocol in TLA+ and model-check progress (`◇ decided`) under a
  `WF`-fair, GST-after-`k` scheduler for small `n` (e.g. `n=4, f=1`), bounded message counts. This is
  precisely how HotStuff was verified for industry (Springer 2021). State the numeric bound (nodes,
  views, depth) explicitly — a bounded check is evidence, not a universal proof.
- **Tamarin/ProVerif exists-trace** — a `progress_reachable` lemma (a decision IS reachable after a
  view-change under a synchrony restriction) is a cheap first artifact in the existing model-first
  pipeline, complementing the safety lemmas. It shows the view-change *can* drive progress; it does not
  show it *must* (that is the TLA+ `◇`).
- **Agda/Coq reference** — Jolteon's Agda formalization (IOG) and Bythos (CCS'24, compositional
  mechanized BFT safety+liveness in Coq) are the SOTA full-liveness mechanizations; porting is a large
  separate effort, cited as the reference standard, not this increment.

**The benchmark point (positioning doc):** ACP model-checks 3 invariants in TLA+ **without stating a
synchrony assumption** — a bounded-liveness check that omits GST is checking liveness in a model where
FLP says it cannot hold universally. DLC-D's contribution here is to state the **GST/partial-synchrony
assumption explicitly** and check progress *relative to it* — the honest version of the same artifact.

## 5. Honest fences (what this document does and does not establish)

- **Design only.** No liveness is proved here. Safety remains the proved core; liveness is conditional on
  partial synchrony and, when built, will be **bounded/model-checked**, not a universal Lean theorem.
- **Aeneas fence.** Any view-change structure goes in the *model* (`lean/DLCD/*` and/or a TLA+/Tamarin
  artifact), never `dlc-core` — the executable core stays translatable and its safety transport intact.
- **Single-decree today.** The committed log is still an oracle; multi-decree Byzantine lift
  (`MultiDecree.log_agreement`'s Byzantine twin) composes per slot and is separate future work.
- **Prior art (web-searched this increment; URLs recorded):**
  - HotStuff — Yin et al., PODC'19 (three-phase, linear view-change): https://arxiv.org/abs/1803.05069
  - HotStuff TLA+/TLC verification (industrial): https://link.springer.com/chapter/10.1007/978-3-030-77448-6_9
  - Liveness Checking of the HotStuff Protocol Family: https://arxiv.org/pdf/2310.09006
  - Jolteon & Ditto (2-chain, async fallback): https://arxiv.org/abs/2106.10362 ; Agda formalization:
    https://github.com/input-output-hk/formal-jolteon
  - "Making Byzantine consensus live" (Gotsman et al., DISC'20): https://software.imdea.org/~gotsman/papers/bftlive-dc.pdf
  - PBFT (Castro–Liskov, OSDI'99, view-change): https://pmg.csail.mit.edu/papers/osdi99.pdf
  - FLP (JACM'85): https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf
  - DLS partial synchrony (JACM'88): https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf
  - Bythos (CCS'24) / TetraBFT (PODC'24) — full mechanized safety+liveness references.
