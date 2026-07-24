# DLC-D Roadmap (updated 2026-07-23, post-R2)

Supersedes the R0–R6 plan (`~/.claude/plans/validated-finding-stardust.md`). This
reflects what R2 actually taught us and re-scopes the remaining phases.

DLC-D is a distributed language whose four guarantee classes are enforced by
construction — **G1** capability & information-flow, **G2** concurrency-safety /
linearizability, **G3** liveness / progress, **G4** convergent consistency — with
the failure model as a first-class type-level contract, carried down to a running
Rust runtime.

## 0. Status snapshot

- **Branch:** `dlc-d/phase0-carve` — **not merged to main.** Latest `27168a2`.
- **Artifact:** 24 Lean libraries, 72 governed theorems, all footprints
  `[propext, Classical.choice, Quot.sound]`; Aeneas drift-gated; CI-gated.
- The **verified model** (G1–G4) and the **machine-checked correspondence from the
  deployed Rust runtime up to that model** are both done. That is the hard, novel
  half of the program.

## 1. Completed phases (condensed)

- **R0 — foundations/governance.** ✅ CI, ledger, expected-axioms, distributed
  spec docs. *Open:* identity reservation in `spec/IDENTIFIERS.md` (name punted).
- **R1 — first-class distributed calculus.** ✅ `command`/`runCmd`/`replicated`,
  capability-gated commit as a typing rule, `FailureBudget` as a graded contract
  (`budgeted_guarantee_voids_over_budget`: behavior is **void exactly over-budget**
  — the mathematical seed of "bounded failure mode"). *Polish backlog deferred —
  see §5.*
- **R2 — verified Rust runtime correspondence.** ✅ (this session, R2.1→R2.4b).
  The deployed `crates/dlc-core` reducer, Aeneas-translated, is machine-checked to
  refine the model; the guarantees transport to the runtime as `rust_*` corollaries
  (`lean/DLCD/Transport.lean`, `TransportConsensus.lean`).
  - **Honest scope (three load-bearing conditions, ledger `DLCD_R2_transport`):**
    (1) **partial-correctness** — holds when the bounded reducer returns `ok`;
    unconditional no-fail is false (an adversarial ≥2³¹-node payload overflows the
    `U32` depth counter — physically unrealizable). (2) **G1 as NI-preservation** of
    the *decoded typed model* (type-labels external); a faithful label decode is
    *provably impossible* (finite hand lattice vs. unbounded runtime labels).
    (3) fair-liveness + the abstract CALM metatheorem are **model-level** (their
    runtime cores are `rust_deliver_correct` / `rust_replicas_converge`).
  - **Bonus:** the correspondence *found and fixed a real deployed-vs-model bug*
    (the reducer was freezing `SaysBind`/`Discharge`; ruled fix-Rust).

## 2. ★ THE NEXT HEADLINE — Failure-modes-as-types (R4+R6 fusion)

**Thesis: make the failure envelope a *type*, and make compilation the proof.**
Turn DLC-D from a proof artifact into a buildable programming model where a
developer writes ordinary async-Rust-looking code and declares one thing — the
service's failure envelope as a type — and `cargo build` green ⟹ the *deployed
binary* provably has exactly those bounded failure modes, and nothing else.

```rust
#[dlc_d::service(budget = Faults<1> & FairDelivery, cap = Write@issuer, flow = χ ⊑ ℓ_low)]
struct Ledger { balance: Replicated<u64> }
```

The type enforces (to the metal, via the R2 correspondence + R3 for the shell):
tolerates exactly 1 fault (over-budget behavior void by construction), every write
capability-gated, flow respects labels, replicas converge. Violations **don't
compile.**

Why reachable *now*: the bounded-failure proof already exists (R1 stage E), the
proof-to-the-metal bridge already exists (R2), and the shell substrate is installed
(R3 RefinedRust).

**Staging:**
- **R6.0 — design + paper prototype (do first).** Nail the `#[dlc_d::service]`
  surface, the three compile-time rejections (un-capability'd write / label leak /
  budget-exceeding path), and how each obligation routes to the verified core.
  **Error ergonomics is a first-class requirement, not polish** — obligation
  failures must read like `rustc` errors, not Lean goals. This is where verified
  systems usually fail the "easy" test.
- **R6.1a — runnable node (the R4 core).** ✅ `crates/dlc-d-node` — thin trusted
  tokio event loop wrapping the verified synchronous transition core; TCB
  enumerated (`spec/r6-1-node-design.md` §5). A cluster converges under
  `cargo run`, and the *deployed* transitions are exactly the R2-corresponded
  functions (`rsm::commit` / `rsm::world_step`, decisions via
  `consensus::decided`), enforced by a source-level purity tripwire rather than
  by intent. Right-reason scenarios included: over-budget crashes **stall without
  diverging** — the runtime shadow of `budgeted_guarantee_voids_over_budget`.
  *Fences:* in-process transport, no leader election, `cap` carried not checked.
- **R6.1b — networked node.** Tamarin model + ProVerif cross-check of the
  replication protocol **first**, then a socket carrier reusing
  `dlc_protocol::wire` verbatim. Deliberately staged this way: `CLAUDE.md` bans
  wire-format changes that outrun the models, so R6.1a introduces no encoding at
  all.
  - **Tamarin model ✅** (`models/tamarin/dlcd-replication.spthy`,
    `spec/r6-1b-replication-protocol.md`): 5 lemmas verified — quorum backing,
    **capability provenance across the wire** (the route to discharging Lean's
    assumed `Authorized` premise), **slot agreement** (`Apply` checks the quorum
    certificate, not the sender — crash-fault, *unless a key is revealed*; NOT
    Byzantine-leader-tolerant, corrected §6.4), plus executability lemmas. Right-reason bite in a separate theory: removing the one-vote-per-slot
    guard makes disagreement **reachable with no key compromise**, and
    `scripts/check-tamarin-bite.sh` gates the *differential* (identical rules;
    the attack falsified in the guarded model) so two independently-green files
    can't pass as evidence. CI job added; Tamarin pinned 1.10.0 → 1.12.0.
  - **ProVerif cross-check ✅** (`models/proverif/dlcd-replication.pv`): the two
    origin properties re-proved under a different prover; it also *found a bug in
    my Tamarin claim* (capability enforcement is redundant leader+voter, so
    `applied_implies_capability` didn't isolate the voter's check — repaired by
    `cap_check_binds_issuer`, added to both models). `slot_agreement` is
    Tamarin-only by a structural limit (linear vote token vs ProVerif's monotonic
    Horn translation).
  - **Authenticated protocol layer ✅** (`crates/dlc-d-node/src/proto.rs`): the
    checks the models demand, implemented — `verify_commit` with no sender
    (forgery-resistant, not Byzantine-tolerant — §6.4), voter-side capability checking, `verify_qc`
    counting **distinct signers** (guards the Nethermind XDC duplicate-signature
    bypass), domain-separated signing, duplicate-member roster rejection. 13 tests
    incl. `tests/authenticated.rs` composing the chain into the verified core.
  - **Authenticated node ✅** (`crates/dlc-d-node/src/auth.rs`, `AuthNode`): the
    whole chain on a live decision path. **Two proof chains kept live at once** —
    `proto` (Tamarin/ProVerif) gates *admissibility*, the Lean-transported
    `decided` predicate makes the *decision*; a forged vote never reaches
    `decided`, a forged commit never reaches `commit`/`world_step`. Replica =
    Ed25519 key, ballot index = roster position (so `rust_consensus_agreement`'s
    shape is preserved). Purity invariant extended to `auth.rs`. Tests: 3-node
    convergence, crash-within-budget, non-member vote ignored, XDC single-signer
    certificate rejected, wrong-command vote ignored, seed/seat mismatch refused.
  - **Wire codec + async transport ✅** (`src/codec.rs`, `src/netauth.rs`): the
    `AuthMsg` CBOR frame (hand-rolled `ciborium::Value`, terms through
    `dlc_protocol::wire` verbatim) + a tokio driver running `AuthNode` with every
    message crossing as bytes. Codec's load-bearing test is *decode still
    verifies* (not `encode∘decode=id`), plus exhaustive single-byte-flip
    corruption rejection. `tests/networked.rs` runs the whole stack (auth +
    `decided` + codec + tokio) to convergence + crash-within-budget +
    over-budget-stall, over the byte transport.
  - **Byzantine quorum threshold ✅** (`proto::Quorum`, `Roster::new_byzantine`):
    the equivocation gap from §6.4 is closed with the standard BFT threshold
    `3·card > 2n` (image of `DLCD.ByzantineConsensus.IsByzQuorum`). Single-round
    safety via honest quorum intersection; `tests/byzantine.rs` runs the *exact*
    §6.4 attack against the Byzantine roster and shows it defeated, plus an
    end-to-end async convergence test.
  - **Byzantine threshold now Aeneas-translated ✅** (`dlc_d_rsm::consensus::
    is_byz_quorum` / `byz_decided`): `Quorum::Byzantine` is cross-checked against
    the translated predicate, as crash is against `is_quorum`. Closed a latent bug
    — the leader tallied crash-quorum regardless of mode (coincides at n=4, wrong
    at n≥7 where it would commit-then-stall); it now dispatches on `roster.quorum()`
    (`byz_decided` for Byzantine). Regression at n=7, end-to-end. Fence that
    remains: the *theorem* transport (`rust_byz_agreement`, needs the honest set as
    a parameter) is backlog; crash has `rust_consensus_agreement`. Byzantine
    *agreement*, not *liveness* (no view change).
  - **Only remaining for R6.1b: literal socket carrier.** The channel carries
    exactly the bytes a socket would, so bind/connect is a carrier swap, not a
    protocol change.
- **R6.2 — the surface + compile-time rejections.** `lark` grammar → AST bridge (or
  a Rust macro front-end); the checker accepts the good program and rejects the
  three violation variants with human errors.
- **R6.3 — the killer demo.** ~30-line replicated register / KV ledger: runs,
  rejects violations at compile time, and the Lean/R2 chain certifies the running
  node's failure envelope. This is the inflection from "proved a model" to "build
  systems this way."

## 3. Re-scoped supporting phases

- **R3 — RefinedRust harness (role narrowed).** R2/Aeneas already verified the
  *pure* transition core, so R3 is now specifically for what Aeneas cannot touch:
  the **concurrent/async shell** (interior mutability, the event loop) refining the
  model. Feeds R6.1. Spike done; RefinedRust ratified; opam switch installed.
- **R5 — IFC-refinement (reshaped by an impossibility finding).** The plan's
  "refine NI into a 1-run SMT setting" assumed a faithful runtime-label decode —
  which R2 proved *impossible* (finite lattice vs. unbounded labels; the NI-relevant
  label is a type-layer artifact absent from executable state). What's realized:
  NI-*preservation* over the Aeneas core (`rust_worldStep_preserves_high`). What's
  open and needs **re-planning, not execution**: whether stronger runtime IFC is
  even the right target, vs. accepting preservation + a typed-label surface (R6) as
  the honest IFC story. **Decision needed before investing.**

## 4. R2 tails (opened this session)

- **Public claim** — README/paper runtime-guarantee wording (you deferred it;
  ledger-only for now).
- **fix-iii** — restrict to a typed-payload class (`CDeriv ⊢ payload : φ⊃φ`) →
  removes the `U32` no-overflow caveat for well-typed commands. Large; layers on
  the partial-correctness form.
- **`rust_log_agreement`** — multi-slot Raft log-matching at the runtime surface
  (single-decree `rust_consensus_agreement` is the load-bearing core).

## 5. Carried-forward backlog

- **CDerivS seal judgment (2.c)** — linear commit-I; validated design, unimplemented.
- **Full `Deriv → CDeriv` swap** — re-prove Decidability / NI / Progress under CARVe.
- **Leader election; BFT liveness** — Byzantine *agreement* now exists both in
  Lean (`DLCD_byz_agreement`) AND at the runtime (`proto::Quorum::Byzantine`,
  R6.1b §6.5); election + BFT liveness / view change (Bythos / TetraBFT lineage)
  don't. Also: Aeneas-translate `ByzantineConsensus` so the runtime Byzantine
  threshold rides a *transported* theorem, not just the Lean definition.
- **Proof fences** — store-type change (partly R1's `replicated φ`); live-log
  scheduling closure.

## 6. Housekeeping / decisions pending

- **Merge `dlc-d/phase0-carve` → main** — all R2 work is unmerged. Decide when.
- **Identity reservation** (`spec/IDENTIFIERS.md`) — the real DLC-D name.
- **README/paper external claim** — your wording call.

## 6b. Hygiene found while landing R6.1a

- **CI clippy was already red** at `crates/dlc-core/src/rsm.rs:198` (and warning in
  `dlc-d-rsm/src/consensus.rs`) under the pinned 1.89 toolchain: `ci.yml` runs
  `clippy --workspace -- -D warnings`, and `needless_range_loop` fires on exactly
  the closure-free indexed loops the Aeneas fence *requires*. Introduced by
  `4bf9ff1` (R2 Arch-1 relocation). Fixed with targeted `#[allow]`s documenting
  why the lint's suggestion is forbidden here — taking it would translate to
  opaque axioms and break the R2 correspondence at that leaf. Aeneas trees
  regenerated (the added doc lines shifted embedded source-location comments;
  diff is comment-only, drift gate clean, 77 snapshots byte-unchanged).

- **`dlc.spthy` soundness caveat — FOUND AND FIXED (2026-07-24).** Under Tamarin
  1.12.0 the delegation model reported a failed message-derivation check
  ("Failed to derive Variable(s): skP, skQ" in `Delegate_Accept` /
  `Discharge_Accept`) with Tamarin appending *"The analysis results might be
  wrong!"* — on a run CI called green, because the gate greps only
  `falsified|incomplete`. Cause: signature checks by pattern-matching
  `sign(msg, skP)` against `!Pk(P, pk(skP))`, which binds the signing key inside
  an adversary-supplied term. Fixed by converting both rules to the
  derivation-clean `verify(sig, msg, pk) = true` idiom (declining the manual's
  `[no_derivcheck]` escape, which would hide the caveat rather than remove it).
  **All 7 lemmas re-proved with identical step counts** — so the properties
  genuinely held and the caveat was on the analysis, not the protocol. Note the
  new idiom makes the adversary *strictly stronger* (semantic verification, not
  syntactic shape-matching), so surviving it is a real result. Both checks
  perturbation-tested: dropping the says-half verification falsifies
  `non_splicing` (6 steps); dropping the evidence verification falsifies
  `no_silent_discharge` (9 steps). CI wellformedness gate now strict for
  `dlc.spthy` as well as the replication models.

## 7. Recommended next thrust

**R6.0 (design + paper prototype of the failure-modes-as-types slice).** It is the
single highest-leverage remaining move: it converts the proven artifact into
something people can build with, it is where "easy AND rigorous" is won or lost
(error ergonomics), and it pulls R3 (shell) and R4 (node) in behind a concrete
goal instead of as abstract phases. R5 stays parked pending a re-plan decision;
the R2 tails and backlog are opportunistic.
