# DLC-D Phase R2 — `dlc-d-rsm`, the verified Rust runtime core (design proposal)

Status: **PROPOSAL ONLY** — no `.rs`/`.lean` edits, no snapshot changes. This
document proposes the first R2 deliverable: a `no_std`, zero-dep,
Aeneas-translatable Rust crate `dlc-d-rsm` that mirrors the Lean RSM
operational model (`lean/DLCD/Rsm.lean` + the safety core of
`lean/DLCD/Consensus.lean`), together with the machine-checked correspondence
by which the guarantees **G1–G4** (proved over the Lean `worldStep`)
**transport** to the Rust core.

Branch `dlc-d/phase0-carve`, HEAD `fcb29fb`. Author's ruling requested on the
Term-bridge option (§5) before implementation.

---

## 0. Prior art (web-searched 2026-07-23; URLs recorded)

The design pattern — *the deployed code refines a proof-assistant-proved
abstract state machine* — and the specific toolchain (Aeneas: Rust →
pure-functional Lean 4):

- **Aeneas: Rust Verification by Functional Translation** (Ho–Protzenko–Fromherz,
  ICFP 2022). The method this whole R2 stage rides on: Charon lifts safe Rust
  to LLBC, Aeneas translates LLBC to a *pure functional* Lean 4 model wrapped
  in a `Result` monad (success / panic / divergence), and one proves the
  extracted model refines a hand-written spec. Chief case study: a resizing
  hash table proved functionally correct.
  - https://arxiv.org/abs/2206.07185
  - https://dl.acm.org/doi/10.1145/3547647
  - https://lean-lang.org/use-cases/aeneas/  (the `Result α` = success|panic|non-termination framing this doc's §5 depends on)
  - https://www.sonho.fr/assets/documents/aeneas.html
- **Aeneas functional-correctness-by-refinement in practice** (RuntimeVerification;
  Plonky3 FRI PoC) — "write a formal spec of what the extracted function should
  do and prove the extracted function matches it"; arithmetic wrapped in
  monads exposing overflow/panic as explicit failure cases (exactly the `U32`
  fence in §5.3).
  - https://runtimeverification.com/blog/from-rust-source-code-to-mathematical-proof
  - https://github.com/runtimeverification/aeneas_fri_fold_arity_verification
- **IronFleet: Proving Practical Distributed Systems Correct** (Hawblitzel et al.,
  SOSP 2015 / CACM). The canonical "implementation refines an abstract
  TLA-style state machine spec" methodology: `SpecInit`/`SpecNext`/`SpecRelation`,
  layered refinement (impl ⊑ protocol ⊑ high-level spec), demonstrated on a
  Paxos RSM (IronRSL). This is the shape our transport theorem instantiates,
  with Aeneas standing in for IronFleet's Dafny.
  - https://www.microsoft.com/en-us/research/publication/ironfleet-proving-practical-distributed-systems-correct/
  - https://www.andrew.cmu.edu/user/bparno/papers/ironfleet-cacm.pdf  (safety + liveness)
- **Verus: A Practical Foundation for Systems Verification** (Lattuada et al.) and
  **A Refinement Methodology for Distributed Programs in Rust**
  (Bila–Pereira–Müller, ETH). The *Rust-native* points of comparison — executable
  Rust proved to refine an abstract spec (Verus's IronSync-style sharded
  refinement). We deliberately choose Aeneas over Verus because DLC's kernel is
  *already* an Aeneas target (`dlc-core`); staying in one toolchain reuses the
  committed `DlcCore` translation.
  - https://www.cs.utexas.edu/~hleblanc/pdfs/verus.pdf
  - https://pm.inf.ethz.ch/publications/BilaPereiraMueller25.pdf
- **Grove: a Separation-Logic Library for Verifying Distributed Systems**
  (Sharma et al., SOSP 2023; Perennial/Iris/Goose over Go). The "verified
  implementation refines an abstract spec" bar in the Iris tradition; reported
  ~12× proof-to-code ratio — a sober external anchor for §9's honest cost.
  - https://iris-project.org/pdfs/2023-sosp-grove.pdf
  - https://arxiv.org/pdf/2309.03046

Takeaway shared by all five: the value is the *machine-checked refinement
square* — "the code you run is provably the state machine you proved about."
R2 supplies that square for DLC-D's RSM, with Aeneas as the extraction engine.

---

## 1. The crate `dlc-d-rsm`

A new **public** workspace member `crates/dlc-d-rsm`, path-dependent on
`dlc-core` (for `Term`, `Prop`, `reduce_with_fuel`). It mirrors, item for item,
`DLCD.Rsm` and the *operational* (non-`Prop`) surface of `DLCD.Consensus`.

### 1.1 Cargo + lib constraints (identical to `dlc-core`)

```toml
# crates/dlc-d-rsm/Cargo.toml
[package]
name = "dlc-d-rsm"
# workspace-inherited version/edition/rust-version
[dependencies]
dlc-core = { path = "../dlc-core" }   # the ONLY dependency; itself Aeneas-clean
```

```rust
#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
extern crate alloc;
```

Must stay inside the same hard fence as `dlc-core` (CLAUDE.md §"Hard
constraints"): **no trait objects, no `async`/futures, no third-party deps
(only `core`/`alloc`/`dlc-core`), no `unsafe`, no interior mutability beyond
Aeneas support**. Add `crates/dlc-d-rsm` to the workspace `members` list (it is
public, unlike the excluded `dlc-grade-quantale`).

### 1.2 The Rust items (each mirrors a real Lean def)

| Rust item (`dlc-d-rsm`) | Lean source of truth | Aeneas-clean? | Notes |
|---|---|---|---|
| `struct FailureBudget { max_faults: u32, fair_delivery: bool, consumed: u32 }` | `DLCD.FailureBudget` | ✓ plain data | `Nat`→`u32`; `zero`/`saturating_add`/`le`/`within_contract` are total bool/arith |
| `enum`-free `struct Command { payload: Term, cap: Option<Prop> }` | `DLCD.Command` | ✓ | `Term`/`Prop` **reused from `dlc-core`** |
| `struct Replica { id: u32, store: Term, applied: u32 }` | `DLCD.Replica` | ✓ | |
| `type CommittedLog = Vec<Command>` | `DLCD.CommittedLog` | ✓ | `List`→`Vec` |
| `struct GlobalConfig { replicas: Vec<Replica>, log: CommittedLog, budget: FailureBudget }` | `DLCD.GlobalConfig` | ✓ | |
| `const APPLY_FUEL: u32 = 1024` | `DLCD.applyFuel` | ✓ | must equal the Lean literal |
| `fn apply_command(c: &Command, s: &Term) -> Term` = `reduce_with_fuel(&app(c.payload, s), APPLY_FUEL).0` | `DLCD.applyCommand` | ✓ | **reuses `dlc_core::reduce::reduce_with_fuel`**; `app` = `Term::App` |
| `fn apply_prefix(init: &Term, cmds: &[Command]) -> Term` (left fold) | `DLCD.applyPrefix` | ✓ | Aeneas handles `slice::iter().fold` as a `Range` loop (same shape as `reduce_with_fuel_loop`) |
| `fn deliver(log: &CommittedLog, r: &Replica) -> Replica` (`log.get(r.applied)` match) | `DLCD.deliver` | ✓ | `List.get?`→`Vec::get`; returns `Option` match, no closure |
| `fn world_step(g: &GlobalConfig) -> GlobalConfig` (`replicas.map(deliver)`) | `DLCD.worldStep` | ⚠ see note | `Vec::iter().map(|r| deliver(&g.log, r)).collect()` — Aeneas translates non-capturing `map` cleanly, but a *capturing* closure (`g.log`) is the one Charon/Aeneas soft-spot; mirror `reduce.rs`'s discipline and write an explicit indexed `for` loop instead of `.map`, exactly as `reduce.rs` spells out `match step(x){..}` rather than `Option::map` |
| `fn is_quorum(card: u32, n: u32) -> bool` = `2*card > n` | `DLCD.IsQuorum` (operationalized) | ✓ | the *decidable* content; the `Finset` form stays Lean-only |
| `fn decided(votes: &[Option<Command>], v: &Command) -> bool` (∃ quorum unanimous) | `DLCD.Decided` (operationalized) | ✓ | quorum witnessed as an index-set `Vec<u32>`; the ∃/∀ `Prop` stays Lean-only |
| `fn commit(g: &GlobalConfig, c: Command) -> GlobalConfig` (append `c` to `log`) | `DLCD.commit` (`CapSafety.lean` L143) — **operational core only** | ✓ | the capability side-condition (`auth : Deriv (issuer says writeCap)`) is a *typing* obligation, not runtime data; the Rust `commit` appends and the authority check is discharged at the `Prop` layer (see §4 fence) |

**`agreement`, `quorum_intersect`, `validity`, `replicas_converge_on_prefix`,
`committed_prefix_agree`** are **theorems** (`Prop`s over `Finset`/`Fin n`),
not executable functions. They do **not** cross into Rust — they are the
*guarantees* the Rust `world_step`/`is_quorum`/`decided` must be shown to
*serve* (§4), not code to translate. This is the correct division: Aeneas
translates the *transition function*; the metatheory stays in Lean.

---

## 2. The central challenge — two `Term`s, two `worldStep`s (the crux)

Aeneas translates `dlc-d-rsm` into a **new** Lean module tree
(`lean/DLCD/Aeneas/DlcDRsm/*`) whose `world_step` is written over Aeneas's
**translated** `dlc_core.syntax.Term` (the enum in
`lean/DLC/Aeneas/DlcCore/Types.lean`). But **G1–G4 are proved over
`lean/DLCD/Rsm.lean`**, whose `worldStep` is written over the **hand-written**
`DLC.Term` (`lean/DLC/Syntax.lean`). So the artifact will contain:

```
  Rust world_step   --Charon/Aeneas-->   DlcDRsm.world_step : dlc_core.syntax.Term-valued  GlobalConfig → Result GlobalConfig
                                                   ≟  (the correspondence to establish)
  proved guarantees                         DLCD.worldStep    : DLC.Term-valued              GlobalConfig → GlobalConfig
```

Two `Term` representations, two `worldStep`s. The transport
`Rust-worldStep ≡ Lean-worldStep` requires **bridging the two `Term`s**. The
two representations differ in three load-bearing ways (this is the crux's real
content, not a formality):

1. **Var indices.** Hand `DLC.Term.var : Nat → Term`; Aeneas
   `syntax.Term.Var : Std.U32 → syntax.Term`. `Nat` is unbounded; `U32` wraps
   at 2³². The decode `U32 → Nat` (`·.val`) is total and injective, but the
   *encode* direction and any `shift`/`subst` that does `i + delta` is only
   faithful while indices stay `< 2³²`.
2. **The `Result` monad.** Every Aeneas function is `… → Result τ`
   (`ok`/`fail`/`div`). Hand functions are pure `… → τ`. Bridging needs a
   **totality lemma**: the RSM functions never return `fail`/`div`.
3. **Fuel & loops.** Hand `reduceWithFuel : Term → Nat → Term × Nat`; Aeneas
   `reduce.reduce_with_fuel : syntax.Term → Std.U32 → Result (syntax.Term × Std.U32)`,
   driven by a `core.ops.range.Range Std.U32` loop
   (`reduce.reduce_with_fuel_loop`). `applyFuel = 1024 < 2³²`, so fuel decodes
   exactly, but the loop's `Range`/`ControlFlow` shape must be related to the
   hand `foldl`.

### 2.1 FINDING — **no `DLC.Term ↔ dlc_core.syntax.Term` bridge exists in-tree**

I checked exhaustively (`grep -rn dlc_core lean/` outside the generated tree;
`grep -rn "import DLC.Aeneas" lean/`):

- **Zero** hand-written Lean files reference `dlc_core.*` or import
  `DLC.Aeneas.DlcCore`. The committed Aeneas tree
  (`lean/DLC/Aeneas/DlcCore/{Types,Funs}.lean`) is **generated and
  drift-gated, but connected to the hand-written model by no proof at all.**
- The only in-tree acknowledgement of the gap is a *comment* in
  `lean/DLC/Subst.lean` (L11–13): "The Aeneas-translated `DLC.Aeneas.DlcCore`
  will contain the Rust functions; a `function_correspondence_subst` lemma (to
  land alongside the substitution lemma's proof) bridges them." That lemma
  **does not exist**; it is future work, described, never inhabited. The same
  is true of the "function-correspondence theorem (see `DLC.Decidability`)"
  advertised in `lean/DLC/Syntax.lean`'s header — `DLC.Decidability` does not
  reference `dlc_core` either.

**Consequence for R2:** option (2a)'s hopeful premise — "is there already a
dlc-core↔DlcCore bridge to reuse?" — is answered **NO**. There is nothing to
reuse. The `Term`-level correspondence (hand `DLC.Term` ↔ Aeneas
`dlc_core.syntax.Term`) and the reducer correspondence (hand `reduceWithFuel` ↔
Aeneas `reduce.reduce_with_fuel`) are **unbuilt for `dlc-core` itself**. R2
must build them — and this is the honest cost sink (§9), because it is *not*
DLC-D-specific: it is the long-deferred `dlc-core` T1-correspondence work,
which R2's reducer bridge should discharge **once, at the `dlc-core` level, for
reuse** rather than privately inside `DLCD.Aeneas`.

The upside of the finding: it clarifies that the reducer bridge is a **shared
`dlc-core` asset**, and that DLC-D's *own* new functions (`deliver`,
`world_step`, `apply_prefix`, `is_quorum`, `decided`, `commit`) are simple
list/fold/arith functions whose refinement squares are cheap *given* the
reducer bridge.

---

## 3. The Term-bridge — options weighed, recommendation

Let `⟦·⟧ : dlc_core.syntax.Term → DLC.Term` be a **decode** (Aeneas → hand),
defined structurally, taking `Var (u : U32) ↦ var u.val`, `App a b ↦ app ⟦a⟧ ⟦b⟧`,
etc. (`Prop`, `Label`, `Principal`, `Obligation` decode analogously). Extend
pointwise to `⟦·⟧_cmd`, `⟦·⟧_rep`, `⟦·⟧_gc` on `Command`/`Replica`/`GlobalConfig`.

### Option (2a) — full isomorphism `DLC.Term ≅ dlc_core.syntax.Term`

Prove a bijection (encode `⌜·⌝ : DLC.Term → dlc_core.syntax.Term` and decode
`⟦·⟧`, with round-trip laws `⟦⌜t⌝⟧ = t`, `⌜⟦u⟧⌝ = u`) and that the two
`worldStep`s commute with it in **both** directions.

- **Pro:** maximally general; supports pulling facts *either* way.
- **Con:** the encode direction is *partial* — `⌜·⌝` on a `var n` with
  `n ≥ 2³²` has no `U32` image, so `⌜·⌝` is either partial or carries a
  well-scoped precondition, and the `⌜⟦u⟧⌝ = u` round-trip needs `u`'s indices
  in-range. You pay for a direction (hand → Aeneas) that the transport theorem
  **never uses**. Heavy, and buys generality R2 does not need.

### Option (2b) — RE-FOUND `DLCD.Rsm` directly on `dlc_core.syntax.Term`

One representation: make `Command.payload`/`Replica.store` be
`dlc_core.syntax.Term`, and `applyCommand` call `dlc_core.reduce.reduce_with_fuel`.

- **REJECTED.** Ripple is catastrophic and it violates the mandate's
  "52 snapshots byte-unchanged":
  - `DLCD.Rsm` sits *under* the entire hand-written DLC metatheory. G1's
    `distributed_noninterference` (`DLCD/DistributedNI.lean`) reuses
    `DLC.t3_two_run_general`; `capability_safety` (`DLCD/CapSafety.lean`) uses
    `DLC.Deriv`/`CDeriv`; `TypedLog`, `LabelFlow`, `Linearizable` all
    pattern-match hand `Term` constructors (`app`/`pair`/`lam`) and quantify
    over hand `Deriv`. **All of that is over `DLC.Term`.** Re-founding `Rsm` on
    the Aeneas `Term` severs `DLCD` from `DLC.Deriv`, `DLC.CDeriv`,
    `t3_two_run_general`, Progress, and every subst lemma — you would have to
    re-prove the *entire* DLC metatheory over `dlc_core.syntax.Term` **in the
    `Result` monad with `U32` indices**. That is not a refactor; it is redoing
    T1–T4 and all 52 guarantees on a hostile representation.
  - Directly contradicts "keep the 52 Lean snapshots byte-unchanged."
  - **Do not pursue.**

### Option (2c) — per-function **decode + refinement squares** ✔ RECOMMENDED

Keep the hand-written `DLCD.worldStep` as the **spec** (unchanged). Define the
one-directional decode `⟦·⟧` (Aeneas → hand) and prove, per function, a
**refinement square** relating the Aeneas image to the hand spec under `⟦·⟧`:

```
  ⟦ DlcDRsm.deliver log r ⟧_rep   = DLCD.deliver ⟦log⟧ ⟦r⟧_rep
  ⟦ DlcDRsm.world_step g ⟧_gc     = DLCD.worldStep ⟦g⟧_gc
  ⟦ DlcDRsm.apply_prefix i cs ⟧   = DLCD.applyPrefix ⟦i⟧ ⟦cs⟧
      DlcDRsm.is_quorum c n        = decide (DLCD.IsQuorum-card c n)     -- bool ↔ Prop
```

This is **exactly Aeneas's own idiom** (§0: "write a spec, prove the extracted
function matches it") — the hand model *is* the spec; the extracted model
refines it. Only the **decode** direction is needed (`fail`/`div`-freedom +
`U32→Nat`), never encode, so none of (2a)'s round-trip/partiality tax is paid.
It touches **no** guarantee proof and **no** snapshot: the 52 stay
byte-identical; R2 is purely *additive* Lean (`lean/DLCD/Aeneas/*` +
`lean/DLCD/Transport.lean`).

**Why (2c) over (2a):** they share the *same* crux sub-lemma (the reducer
square, §3.1); (2c) is (2a) minus the encode direction and the round-trip laws
— strictly less work for exactly the generality the transport theorem needs
(pull guarantees *from* hand *to* Aeneas/Rust, one direction).

### 3.1 The crux sub-lemma (shared, `dlc-core`-level, reusable)

Everything reduces to one square about the **reducer**, which is a `dlc-core`
asset (not DLC-D-specific), and its two honest side-conditions:

```
theorem reduce_with_fuel_refines
    (t : dlc_core.syntax.Term) (f : Std.U32)
    (hwf : WellScoped t)              -- (i) indices small enough that no
                                      --     shift/subst does a U32 overflow
                                      --     within f steps  → no `fail`
    : (dlc_core.reduce.reduce_with_fuel t f).run       -- Result → value (ii)
        = ((DLC.reduceWithFuel ⟦t⟧ f.val))             -- pure hand model
```

- **(i) The `U32` fence — must NOT be hand-waved (REALIZABLE gate).** The
  Aeneas `subst`/`shift` on `U32` indices exposes `i + delta` overflow as a
  `Result.fail` path that the hand `Nat` model cannot have. The square holds
  **only** on `WellScoped` terms (indices + maximal shift-depth over the run
  stay `< 2³²`). This is a *genuine* precondition, benign for the RSM (payloads
  are small closed store-transformers) but **it is the soundness content of the
  bridge and must be a stated hypothesis**, not an assumption. `WellScoped` is
  a decidable structural predicate; the RSM anti-vacuity payload
  (`λ_. ⟨0,0⟩`, `Rsm.lean` L245) trivially satisfies it, giving a non-vacuous
  witness.
- **(ii) `fail`/`div`-freedom.** `reduce_with_fuel` is fuel-bounded (no `div`);
  under `WellScoped` it emits no `fail`. Discharged by induction on fuel using
  the per-`step` no-fail lemma. This is the "`Result α` = success|panic|
  non-termination, and we prove it's always success" move (§0, lean-lang).

**This lemma is the long-deferred `function_correspondence_subst` /
`dlc-core` T1-correspondence work** flagged in `Subst.lean`. R2 should land it
in `lean/DLC/Aeneas/Correspondence.lean` (a `DLC`-level file), so both DLC's
own T1 and DLC-D's transport consume it. Given it, `apply_command`'s square is
one rewrite, and the structural squares (`deliver`/`world_step`/`apply_prefix`)
are list-algebra (`map`/`foldl`/`get?` commuting with `⟦·⟧`).

---

## 4. The transport theorem — "the Rust core satisfies G1–G4"

**Target statement** (the R2 headline; lands in `lean/DLCD/Transport.lean`):

```
theorem rust_world_step_correct (g : DlcDRsm.GlobalConfig) (hwf : WellScopedGC g) :
    ⟦ (DlcDRsm.world_step g).run ⟧_gc = DLCD.worldStep ⟦g⟧_gc
```

i.e. **the Aeneas image of the Rust `world_step` equals the hand-written
`DLCD.worldStep` under the decode**, on well-scoped configs. Proof: unfold
`world_step` = indexed `deliver` over `replicas`; apply the `deliver` square
(which calls the `apply_command` square, which calls §3.1); `map`/decode
commute.

**Composition into G1–G4.** Because `world_step` *equals* `worldStep` under
`⟦·⟧`, every guarantee proved over `worldStep`/`applyPrefix`/`deliver` pulls
back to the Rust image. Concretely, the convergence seed (G4) transports as:

```
theorem rust_replicas_converge
    (h1 : AppliedPrefix ⟦init⟧ ⟦log⟧ ⟦r1⟧_rep)
    (h2 : AppliedPrefix ⟦init⟧ ⟦log⟧ ⟦r2⟧_rep)
    (hlen : r1.applied = r2.applied) :
    ⟦r1.store⟧ = ⟦r2.store⟧
  := replicas_converge_on_prefix h1 h2 (by simpa using hlen)   -- via §3 squares
```

and analogously the safety guarantees over the *operational* consensus surface
(`is_quorum`/`decided`) discharge `agreement`/`committed_prefix_agree`'s
executable premises. The pattern is uniform: **decode the Rust state, invoke
the existing hand-side guarantee, re-encode the conclusion through `⟦·⟧`.** No
guarantee is re-proved; each is *transported*.

**What is a typing-layer fence, not a Rust obligation.** `commit`'s capability
gate (`auth : Deriv (issuer says writeCap)`, `CapSafety.lean`) and G1's
non-interference are `Prop`-level facts about *derivations*, not runtime data;
the Rust `commit` carries the `Command` but not its `Deriv`. So
`capability_safety`/`distributed_noninterference` transport as statements about
the **decoded log's typing**, exactly as they already fire on hand logs — the
Rust core does not weaken them, and does not (cannot) re-establish them at
runtime. This is the honest scope: R2 transports the **operational** guarantees
(convergence, linearizability seed, delivery/fold behavior, quorum safety
predicates); the **typed** guarantees remain `Prop`-level over the decoded
state, unchanged.

### 4.1 `[RE-PROVE]` vs `[RE-FOUND]` ledger

- `[UNCHANGED]` — the 52 guarantees over `DLCD.worldStep`/`Consensus`. Byte-identical. They are the spec side of the refinement; R2 never edits them.
- `[RE-PROVE — NEW, `dlc-core`-level, reusable]` — the reducer square §3.1 (`reduce_with_fuel_refines`) + the `⟦·⟧` decode + the no-fail/`WellScoped` lemmas. This is the crux and the cost sink; it doubles as `dlc-core`'s own unbuilt T1-correspondence.
- `[RE-PROVE — NEW, cheap]` — the DLC-D structural squares (`deliver`, `world_step`, `apply_prefix`, `is_quorum`, `decided`, `commit`) + the transport corollaries §4. List/fold/arith algebra given §3.1.
- `[RE-FOUND]` — **none.** Option (2b) rejected; nothing in `DLC`/`DLCD` is re-founded.

---

## 5. Extending the drift gate (a second Charon target)

Today `scripts/{check-drift,aeneas-translate}.sh` and `.github/workflows/aeneas.yml`
are **hardcoded** to one target: `crates/dlc-core` → `lean/DLC/Aeneas/DlcCore`,
via the composite action `coproduct-opensource/aeneas-ci@v1.0.2` with inputs
`rust-source-dir` / `lean-output-dir`. `dlc-d-rsm` is a **second** target.

**Mechanics.** `dlc-d-rsm` depends on `dlc-core`, so
`charon cargo --preset aeneas` run in `crates/dlc-d-rsm` emits a single
`dlc_d_rsm.llbc` that *includes `dlc-core`'s items* (Charon preserves crate
provenance: `dlc_core.*` vs `dlc_d_rsm.*` namespaces). Aeneas `-split-files`
then emits **both** a `DlcCore/*` tree and a `DlcDRsm/*` tree.

**Recommended gate shape (single invocation, dual diff):**
1. Parameterize `aeneas-translate.sh`/`check-drift.sh` over `(crate-dir,
   out-dir, crate-stem)` (an arg or a small target table), keeping the current
   `dlc-core` call as target #1.
2. Add target #2: `crates/dlc-d-rsm` → `lean/DLCD/Aeneas/DlcDRsm`.
3. **Soundness cross-check:** the `dlc_core.*` files Aeneas re-emits while
   translating `dlc-d-rsm` must match the **already-committed**
   `lean/DLC/Aeneas/DlcCore/*` **byte-for-byte**. A mismatch means the
   `dlc-d-rsm` build perturbed `dlc-core`'s translation — a real drift, fail.
   (This makes the two targets mutually consistent rather than independently
   floating.)
4. `.github/workflows/aeneas.yml`: extend both `paths:` filters with
   `crates/dlc-d-rsm/**` and `lean/DLCD/Aeneas/**`, and add a second
   `aeneas-ci` step (`rust-source-dir: crates/dlc-d-rsm`,
   `lean-output-dir: lean/DLCD/Aeneas/DlcDRsm`) — or a matrix over the two
   targets. Keep the **same pinned** Charon/Aeneas pair; both trees must build
   against the one `require aeneas @ <rev>` in `lean/lakefile.lean`.
5. `lean/DLCD/Aeneas/DlcDRsm.lean` re-exports the generated modules (mirror of
   `lean/DLC/Aeneas/DlcCore.lean`); `lake build DLCD.Aeneas.DlcDRsm` gates
   compilation.

---

## 6. Impact map + the minimal first sub-increment (R2.1)

R2 is explicitly **multi-increment**. The minimal first sub-increment ships the
*mirror + translation + gate* — the refinement **squares are R2.2+**.

### R2.1 (do first — skeleton, translation, gate; NO correspondence proof)
- **New** `crates/dlc-d-rsm/{Cargo.toml,src/lib.rs}` — the §1.2 items
  (`FailureBudget`, `Command`, `Replica`, `GlobalConfig`, `apply_command`,
  `apply_prefix`, `deliver`, `world_step`, `commit`, `is_quorum`, `decided`),
  `no_std`/`forbid(unsafe)`/dep-only-`dlc-core`, with unit tests mirroring
  `Rsm.lean`'s anti-vacuity example (`dup` payload → `⟨0,0⟩`).
- **Edit** root `Cargo.toml` `members` (+`crates/dlc-d-rsm`).
- **New** `lean/DLCD/Aeneas/DlcDRsm/*` + `lean/DLCD/Aeneas/DlcDRsm.lean`
  (generated, committed).
- **Edit** the two drift scripts + `aeneas.yml` (§5).
- **Gate:** `check-drift` green on the new target; `lake build
  DLCD.Aeneas.DlcDRsm` compiles; `check-claims.sh` green; **52 snapshots
  byte-unchanged** (no `lean/DLCD/*.lean` guarantee file touched).
- **Explicitly NOT in R2.1:** the decode `⟦·⟧`, `reduce_with_fuel_refines`, the
  squares, the transport corollaries. R2.1 proves *nothing* about
  correspondence — it establishes the translated artifact + the diff gate so
  the correspondence has a fixed target to refine against.

### R2.2 — decode + structural squares
`⟦·⟧` (`lean/DLCD/Aeneas/Decode.lean`); the cheap squares (`deliver`,
`world_step`, `apply_prefix`, `is_quorum`, `decided`, `commit`) **assuming**
the reducer square as a hypothesis/`sorry`-free `axiom`-free *stated* lemma.

### R2.3 — the crux (`dlc-core`-level reducer correspondence) ← cost sink
`lean/DLC/Aeneas/Correspondence.lean`: `WellScoped`, no-fail lemma,
`reduce_with_fuel_refines` (§3.1). Discharges R2.2's hypothesis **and** the
long-deferred `function_correspondence_subst`. Shared with `dlc-core`'s T1.

### R2.4 — transport corollaries
`lean/DLCD/Transport.lean`: `rust_world_step_correct`, `rust_replicas_converge`,
the G1–G4 pull-backs (§4). Optionally re-export in `DLCD.Summary` under a new
"R2 — the Rust core refines the model" heading (additive; no existing line
changes).

---

## 7. Honest cost

| Increment | What | Rough size | Risk |
|---|---|---|---|
| R2.1 | crate skeleton + Aeneas translation + drift gate | ~250–350 LOC Rust + generated Lean + ~60 LOC scripts/CI | **Low.** Mechanical mirror; the only Rust risk is keeping `world_step` closure-free (mitigated: explicit `for` loop per `reduce.rs`'s own discipline). Charon multi-crate translation is the one *unproven-locally* step (dlc-core's translation is proven to work; dlc-d-rsm's dependency pull-in is new — verify Charon emits a clean dual tree under the pin). |
| R2.2 | decode + structural squares | ~200–300 LOC Lean | **Low–med.** List/fold algebra; standard. |
| R2.3 | **reducer correspondence (the crux)** | **large** — this is the unbuilt `dlc-core` T1-correspondence: `⟦·⟧` over full `Term`/`Prop`, `WellScoped`, no-`fail` induction over `step`'s ~10 arms + congruence, `Result`/`Range`/`ControlFlow` loop-vs-`foldl` reconciliation, `U32↔Nat` shift/subst faithfulness | **High.** External anchor (§0): Grove reports ~12× proof:code; Aeneas reducer/subst correspondences are known-nontrivial. Expect this to dominate R2 and to want its own sub-increments (subst square → step square → fuel-loop square). **This cost is not new debt R2 invents — it is pre-existing `dlc-core` debt R2 is forced to (and should) pay, once, reusably.** |
| R2.4 | transport corollaries | ~150 LOC Lean | **Low** given R2.3. |

**Bottom line:** R2.1 is a clean, low-risk, self-contained deliverable that
produces a real artifact (verified-transition-core *skeleton* + drift gate)
without over-claiming. The *guarantee transport* is real but back-loaded onto
R2.3, whose weight is the `dlc-core` reducer correspondence that the repo has
deferred since the `Subst.lean` comment. Do **not** advertise "the Rust core
satisfies G1–G4" until R2.4; until then the honest claim is "the Rust core is
the Aeneas-translated, drift-gated mirror of the proved model; the refinement
theorem is in progress."

---

## 8. Open questions for the author's ruling

1. **Term-bridge option — confirm (2c)?** Recommendation is **(2c)** per-function
   decode + refinement squares (one-directional; Aeneas-idiomatic; 52 snapshots
   untouched), **rejecting (2b)** (severs DLCD from all hand `DLC.Term`
   metatheory; violates byte-unchanged) and preferring it over **(2a)** (pays
   for an unused encode direction + round-trip laws). Ruling?
2. **Is there an in-tree `dlc-core↔DlcCore` correspondence to reuse?**
   **Answered: NO** (§2.1). Nothing references `dlc_core.*` outside the
   generated tree; `function_correspondence_subst` is a comment, not a lemma.
   **Ruling needed:** land the reducer correspondence (§3.1) as a **shared
   `dlc-core`-level** file (`lean/DLC/Aeneas/Correspondence.lean`) so it serves
   *both* DLC's T1 and DLC-D's transport — vs. a private `DLCD.Aeneas` copy?
   (Recommend shared.)
3. **The `U32` `WellScoped` fence.** Is a stated well-scopedness precondition on
   the transport theorem acceptable (recommended: yes — it is the sound,
   honest content of the `U32` vs `Nat` gap, benign for RSM payloads), or do
   you want the Rust `Term` var index widened / a saturating-index discipline
   to make it unconditional? (Recommend: keep the precondition; do not perturb
   `dlc-core`'s `u32` index.)
4. **Drift-gate shape.** Single Charon invocation on `dlc-d-rsm` with a dual
   diff (DlcCore cross-check + DlcDRsm) — vs. two independent invocations?
   (Recommend single-invocation/dual-diff for mutual consistency.)
5. **R2.1 scope confirm.** Ship skeleton + translation + gate with **zero**
   correspondence proof (the refinement is R2.2–R2.4)? Confirms the honest
   staging and keeps R2.1 low-risk.
6. **`commit` mirror.** Include the operational `commit` (append-only) in the
   Rust crate now, with the capability gate explicitly a `Prop`-layer fence
   (§4), or defer `commit` entirely to a later increment since its guarantee is
   typing-level, not operational? (Recommend include the append-only operation;
   fence the authority check.)
