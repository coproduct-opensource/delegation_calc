# R6.0 — Failure-modes-as-types: the developer surface (design + paper prototype)

*Design memo. 2026-07-23. Branch `dlc-d/phase0-carve`, HEAD `7807050`. DESIGN-ONLY:
nothing here is committed to source; no crate, Lean file, or ledger was edited. The
one artifact besides this doc is a non-compiled macro-expansion sketch under the
session scratchpad.*

Supersedes nothing; realizes roadmap §2 (`spec/dlc-d-roadmap.md`) and the IFC-2 frame
of `spec/r5-ifc-replan.md`. This is R6.0 — the paper prototype that nails the
`#[dlc_d::service]` surface, the three compile-time rejections, and how each obligation
routes to the already-verified core. It does NOT write the macro (R6.2) or the node
(R6.1); it specifies them and fixes the discharge architecture so those phases have a
checkable target.

---

## 0. Thesis and the standard it must meet

Make the failure envelope a **type** and make **compilation the proof**. A developer
writes ordinary async-Rust-looking code and declares one thing — the service's failure
envelope:

```rust
#[dlc_d::service(budget = Faults<1> & FairDelivery, cap = Write@issuer, flow = χ ⊑ ℓ_low)]
struct Ledger { balance: Replicated<u64> }
```

`cargo build` green ⟹ the deployed binary provably has **exactly** those bounded failure
modes and nothing else. Violations do not compile.

Two standards, both first-class:

- **Rigorous to the core.** Each declared bound must discharge into a *machine-checked*
  theorem transported to the deployed Rust binary — not a lint, not a runtime assertion.
  The verified assets already exist (§1); the surface's whole job is to route to them.
- **Easy.** Obligation failures must read like `rustc` errors — source-located, one
  problem, one fix — **not** like Lean goals. This is where verified systems fail the
  "easy" test, so it is treated as a requirement (§4), not polish.

---

## 1. The verified assets this surface sits on (what each obligation routes to)

Every obligation the surface emits must terminate at one of these. They are done and
governed (footprint `[propext, Classical.choice, Quot.sound]`).

| Axis | Model theorem | Transported (to the metal) | File |
|------|---------------|----------------------------|------|
| **Budget** | `DLCD.budgeted_guarantee_voids_over_budget` — `BudgetedGuarantee f b G` is *uninhabited* at grade `b = f⊕1`, for every payload `G` | `FailureBudget.budgetedGuarantee_of_withinContract` bridges the runtime `FailureBudget{max_faults, fair_delivery, consumed}` struct into the grade | `lean/DLCD/FaultGrade.lean` |
| **Capability** | `DLCD.capability_safety` (log provenance) + `DLCD.capability_safety_by_inversion` (typing-native: recovers the `says`-credential from the `commit-I` *type*) | `DLCD.Transport.rust_capability_safety` via `commit_square` | `lean/DLCD/CapSafety.lean`, `lean/DLCD/Transport.lean` |
| **Flow (IFC)** | `DLCD.distributed_noninterference` + `LowEquivG ℓLow (Prop'.at χ ℓhigh)` | `DLCD.Transport.rust_distributed_noninterference` and `_low` (IFC-1) | `lean/DLCD/DistributedNI.lean`, `lean/DLCD/TransportNI.lean` |
| **Metal bridge** | R2 correspondence squares (`world_step_square`, `apply_prefix_square`, `deliver_square`, `commit_square`) — decode `⟦·⟧` matches the model **when the generated op returns `ok`** | *is* the transport route | `lean/DLCD/Transport.lean` |
| **Runnable substrate** | `dlc_core::rsm` — `FailureBudget / Command / Replica / GlobalConfig / world_step / commit / apply_prefix / deliver`; Aeneas-verified, pure (no async/unsafe/deps) | `crates/dlc-d-rsm` owns the consensus tree | `crates/dlc-core/src/rsm.rs` |

The load-bearing runtime shapes the surface targets:

```rust
struct Command      { payload: Term, cap: Option<Prop> }
struct Replica      { id: u32, store: Term, applied: u32 }
struct GlobalConfig { replicas: Vec<Replica>, log: CommittedLog, budget: FailureBudget }
enum   Prop         { …, Says(Principal, Box<Prop>), At(Box<Prop>, Label),
                          Replicated(Box<Prop>, Label) }
```

The `commit-I` typing rule (`lean/DLC/Judgment.lean :: Deriv.commitI`) is the pivot for
two of the three axes:

```
Γ ⊢ c : issuer says capProp     Γ ⊢ M : φ ⊃ φ
─────────────────────────────────────────────────  commit-I
Γ ⊢ command(M, c, ℓ) : Replicated (φ ⊃ φ) ℓ
```

It demands (a) a **credential** subterm `c` — the capability axis — and (b) a **store
transformer** `M : φ ⊃ φ` that is a *type-endomorphism* — the flow axis's per-write
obligation. `ℓ` is the store's classification label — supplied by `flow=`.

---

## 2. Surface syntax

### 2.1 Front-end recommendation: **Rust attribute proc-macro** (not the lark grammar)

Recommend the roadmap's alternative — a Rust proc-macro `#[dlc_d::service(...)]` plus
`#[dlc_d::write]` / `#[dlc_d::read]` — over the lark-grammar→AST bridge. Justification:

1. **rustc IS the error surface.** The "easy" requirement is *error ergonomics*
   (§4). In a proc-macro, source spans are already in hand; `syn::Error::to_compile_error`
   emits genuine `rustc` diagnostics with carets at the offending token, for free. A
   standalone grammar means rebuilding a parser, a type-checker, *and* a diagnostic
   renderer with span reconstruction — i.e. rebuilding rustc, worse. The single place
   verified systems lose "easy" is exactly the place a proc-macro wins by default.
2. **Stay in Rust.** The developer writes ordinary async-Rust and adds attributes; no
   new toolchain, no new language, `cargo build` unchanged. This is the roadmap's "writes
   ordinary async-Rust-looking code."
3. **Reuse the crates as a library.** The macro emits Rust that references `dlc_core`
   types (`Command`, `Prop`, `FailureBudget`) and the R2/R3 substrate directly. A grammar
   front-end would need a separate elaboration path to those same types.
4. **The only thing a grammar buys** — a non-Rust surface language — is not a goal;
   the goal is to make *Rust* services carry the envelope.

**Tradeoff (honest):** a proc-macro cannot see across crate/function boundaries the way a
whole-program checker could, and macro-level type reasoning is limited (it sees syntax,
not resolved types). The design handles this by splitting obligations into a Tier-1 that
the *Rust typechecker* (post-expansion) discharges and a Tier-2 that a build-time check
against the verified core discharges (§3) — the macro emits code, the compiler and the
core do the checking.

### 2.2 The three axes as declarative attributes

```rust
#[dlc_d::service(
    budget = Faults<1> & FairDelivery,   // tolerate exactly 1 crash fault; fair delivery
    cap    = Write @ issuer,             // every write gated by a Write cap issued by `issuer`
    flow   = χ ⊑ ℓ_low,                  // store classification χ may flow only up to ℓ_low
)]
struct Ledger {
    #[replicated] balance: Labeled<u64, χ>,
}
```

- `budget = Faults<f> & FairDelivery` → const-generic fault bound `Faults<f>` + the
  `fair_delivery` flag of the runtime `FailureBudget`.
- `cap = Write @ issuer` → each `#[write]` method demands a `Cap<Write, Issuer>` token.
- `flow = χ ⊑ ℓ` → the store field's phantom label `χ` and the observer ceiling `ℓ`,
  supplied as the **external typing parameters** the NI theorems consume (§3.3).

**Unicode vs ASCII (open, §9).** `χ ⊑ ℓ_low` mirrors the spec but is hostile to type on a
US keyboard and to `syn` tokenization. Recommend accepting an ASCII alias
(`flow = chi <= l_low`) as the canonical form with the Unicode form as sugar.

### 2.3 A full ~30-line service (the R6.3 target program)

```rust
use dlc_d::{service, write, read, Cap, Write, Labeled, Replicated};

// Classification lattice for THIS service (two points suffice for the demo).
dlc_d::labels! { χ = secret;  ℓ_low = public;  χ ⋢ ℓ_low }   // secret does NOT flow to public

#[dlc_d::service(budget = Faults<1> & FairDelivery, cap = Write @ issuer, flow = χ ⊑ ℓ_low)]
struct Ledger {
    #[replicated] balance: Labeled<u64, χ>,      // the replicated register, classified secret
}

impl Ledger {
    #[dlc_d::write]                              // capability-gated mutation (commit-I credential)
    fn credit(&mut self, _cap: Cap<Write, issuer>, amount: u64) {
        self.balance = self.balance.map(|b| b.saturating_add(amount));  // endomorphism u64→u64
    }

    #[dlc_d::read(label = ℓ_low)]                // a public read: must be a sanctioned downgrade
    fn published_balance(&self, policy: BalancePolicy) -> Labeled<u64, ℓ_low> {
        self.balance.declassify(policy)          // IFC-5 sanctioned flow (see §8 gap)
    }
}

fn main() -> dlc_d::Result<()> {
    let node = dlc_d::Node::<Ledger>::bootstrap(dlc_d::Cluster::from_env())?;
    node.run()                                   // thin trusted tokio loop over world_step (R6.1)
}
```

Everything above `main` is the *declared envelope*; `main` is the trusted shell (§5). The
attributes are the entire proof burden — `cargo build` green certifies the envelope.

---

## 3. The discharge architecture

**One-paragraph summary.** The macro elaborates the three attributes into three
obligations and discharges them in two tiers. *Tier 1 (typed away — cheap, local, the
Rust typechecker):* the surface encoding turns each bound into a Rust type constraint —
an un-capability'd write cannot name the `Cap` token it needs, a secret value cannot
unify with a public slot, and an over-budget handler cannot satisfy the `Faults<f>` const
bound — so the *shape* violations are ordinary type errors with no proof obligation left.
*Tier 2 (metal-backed — the verified core):* for the programs that pass Tier 1, the macro
emits, per service, a set of proof obligations — a `Deriv`/`PropDeriv` witness that the
store field types at `Prop'.at χ ℓ` and each write body is a `φ ⊸ φ` endomorphism, plus
the `WellFormedLog` commit provenance and the external `(χ, ℓ)` parameters — that are
*checked* (not asserted) to instantiate the transported theorems `rust_capability_safety`,
`rust_distributed_noninterference{,_low}`, and `budgeted_guarantee_voids_over_budget`. The
boundary: **shape is typed away by the surface encoding; the guarantee-to-the-metal is
carried by R2 (partial correctness, conditioned on the runtime returning `ok` / no U32
overflow) and IFC-1 (χ/ℓ supplied from the `flow=` attribute as the external parameter,
never recovered from runtime bytes).** `cargo build` green is the conjunction of both
tiers.

### 3.1 What Tier 1 types away (Rust typechecker, no core needed)

- **Capability shape.** `#[dlc_d::write] fn credit(&mut self, cap: Cap<Write, Issuer>, …)`.
  `Cap<Write, Issuer>` is a token type whose only constructors live behind the grant path.
  A caller without a token in scope simply cannot form the call. This is the surface shadow
  of `commit-I`'s credential premise — the same "constructor demands the proof as an
  argument" discipline `DLCD.commit` uses in Lean.
- **Flow shape.** Labels are phantom type parameters (`Labeled<T, L>`); `χ ⋢ ℓ_low` from
  `labels!` means `Chi: FlowsInto<LLow>` is *not* implemented, so returning a
  `Labeled<_, Chi>` where `Labeled<_, LLow>` is expected fails to unify. The only bridge is
  `declassify` (Tier-2 sanctioned flow).
- **Budget shape.** `Faults<f>` is a const generic; a handler that structurally requires
  tolerating `f+1` faults is parameterised at a grade the `Faults<f>` bound rejects.

Tier 1 is where "reads like rustc" is *automatic* — these are literally rustc type errors,
re-worded by the macro's diagnostic layer (§4).

### 3.2 What Tier 2 discharges against the verified core

Tier 1 rejects malformed *shapes*; it does not by itself prove the *guarantee holds to the
metal*. Tier 2 emits, into a generated `__<service>_obligations` module, three checked
instantiations:

- **`cap_gate`** — every commit path builds `Command { cap: Some(Says(issuer, writeCap)) }`
  carrying a `Deriv` credential witness ⟹ instantiate `rust_capability_safety`
  (route: `commit_square` + `capability_safety`). The `commit-I` inversion
  (`capability_safety_by_inversion`) means the witness is recoverable from the command's
  *type*, so the macro need only emit a well-typed `command(M, c, ℓ)`; the credential is
  latent in it.
- **`store_type`** — the `#[replicated]` field elaborates to `Prop'.at χ ℓ` (χ, ℓ from
  `flow=`), and each `#[write]` body elaborates to `PropDeriv [] payload (φ ⊸ φ)` ⟹
  instantiate `rust_distributed_noninterference` (high case) and `_low` (the endomorphism
  case), with `ℓLow := ℓ`, `χ := χ` as **external parameters**.
- **`budget`** — the service's guarantee is delivered at `FaultGrade ≤ f` ⟹ instantiate
  `budgeted_guarantee_voids_over_budget` via `FailureBudget.budgetedGuarantee_of_withinContract`
  (over `f`, the guarantee *type* is void by construction).

**The check must actually run** (this is "compilation is the proof," not a stub): the
Tier-2 obligations are checked against the real theorems, e.g. by a build-time step that
elaborates the emitted `Deriv`/`PropDeriv` terms and confirms they instantiate the governed
statements. The trust/speed model for that step is an open question (§9) — options range
from regenerating Lean and running `lake build`, through a RefinedRust check on the emitted
shell, to a lighter Rust-side certificate checker over the emitted obligation terms.

### 3.3 How the flow axis uses IFC-1 (the external-parameter hinge)

The decode-impossibility (`Transport.lean` §7 ★★★; `r5-ifc-replan.md` §1.2) proved you
cannot *read* a classification back out of the executable `Vec U32` bytes — the runtime
carries no store types. IFC-2 (this surface) sidesteps the decode entirely: it **carries
the classification forward from the source**. The developer writes `flow = χ ⊑ ℓ`; the
macro compiles that into (a) the store-type obligation `Prop'.at χ ℓ` on the field and (b)
the per-write endomorphism obligation — which are *exactly* the external parameters
`rust_distributed_noninterference{,_low}` already consume. The `ℓhigh`/`ℓLow` now have a
real object to attach to — the type the developer wrote, checked at build time — and NI
becomes a statement about *runtime-typed programs* (programs that compiled under the
`service` obligation): "this compiled ⟹ its store field carries `Prop'.at χ ℓ` ⟹ its
deployed multi-step execution preserves `LowEquivG` at that type (IFC-1) ⟹ a `ℓ`-observer
cannot distinguish it from any low-equivalent run." The `Vec U32` bytes never enter the
argument. This is precisely why `r5-ifc-replan.md` concludes "invest in IFC" and "build
failure-modes-as-types" are the *same move*: IFC-2 = R6's `flow` axis.

---

## 4. Error ergonomics (FIRST-CLASS)

The rule: **a developer never sees a Lean goal.** Every obligation failure surfaces as a
source-located `rustc`-style diagnostic naming (a) the offending line, (b) the violated
declared bound, and (c) one concrete fix. Tier-1 failures are rustc errors already; the
macro re-labels them. Tier-2 failures are the danger — a raw `PropDeriv` goal would sink
"easy" — so the macro *catches* Tier-2 failures and re-renders them; it must never pass a
Lean goal through.

**Rejection 1 — un-capability'd write.**
```
error[dlc_d::cap]: write to replicated store without a capability
  --> ledger.rs:14:9
   |
14 |         self.balance = self.balance.map(|b| b + amount);
   |         ^^^^^^^^^^^^ this mutation commits to the replicated log
   |
   = note: `#[service(cap = Write @ issuer)]` requires every write to carry a
           `Cap<Write, issuer>` capability
   = help: take the capability as a parameter:
             fn credit(&mut self, cap: Cap<Write, issuer>, amount: u64)
   = note: enforced by construction — DLC-D `commit-I` demands the `says`-credential
           (theorem: DLCD.rust_capability_safety)
```
(Before: `error[E0412]: cannot find type Cap in this scope` / a raw missing-argument
error. After: the message above.)

**Rejection 2 — label leak (flow violation).**
```
error[dlc_d::flow]: secret value flows to a public sink
  --> ledger.rs:19:9
   |
19 |         return self.balance;              // Labeled<u64, χ>
   |                ^^^^^^^^^^^^ classified `χ = secret`, returned where `ℓ_low = public` is required
   |
   = note: `#[service(flow = χ ⊑ ℓ_low)]` forbids `secret ⋢ public`
   = help: if this downgrade is intended, route it through a sanctioned declassify:
             self.balance.declassify(policy)
   = note: enforced by construction — distributed noninterference at the store type
           (theorem: DLCD.rust_distributed_noninterference)
```
(Before: `error[E0308]: mismatched types: expected Labeled<u64, LLow>, found Labeled<u64, Chi>`.
After: the message above, framed as a flow violation with the declassify escape hatch.)

**Rejection 3 — budget-exceeding path.**
```
error[dlc_d::budget]: operation exceeds the declared fault budget
  --> ledger.rs:22:9
   |
22 |         self.commit_requiring_two_failures();
   |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ tolerates 2 faults; service declares Faults<1>
   |
   = note: `#[service(budget = Faults<1> & FairDelivery)]` bounds the envelope at 1 fault
   = note: over budget, the guarantee TYPE is void by construction — there is no run in
           which this path both exceeds the budget and keeps the guarantee
           (theorem: DLCD.budgeted_guarantee_voids_over_budget)
   = help: raise the budget to `Faults<2>` (and prove 2-resilience) or make the path
           tolerate ≤ 1 fault
```

The Tier-2 re-render is the genuine work (§8): the macro must map a failed obligation back
to its source span and declared bound. This is *not* standard proc-macro plumbing.

---

## 5. The runnable node (R6.1) and the honest TCB

R6.1 is a thin, **trusted** async shell wrapping the verified synchronous core. The node
runs a tokio event loop that, per tick, calls the Aeneas-verified `dlc_core::rsm::world_step`
(deliver → apply → advance) over the `GlobalConfig`, and gossips the log to peers.

```
        ┌─────────────────── TRUSTED SHELL (TCB) ───────────────────┐
        │  tokio event loop  ·  transport (net)  ·  clock  ·  wire   │
        │  serialization (dlc-protocol/CBOR)  ·  the proc-macro      │
        └───────────────┬───────────────────────────────────────────┘
                        │ calls, per tick
        ┌───────────────▼───────────────────────────────────────────┐
        │  PROVEN CORE:  dlc_core::rsm::world_step / commit / …       │
        │  Aeneas-verified pure transition; R2 squares; transports    │
        │  rust_capability_safety · rust_distributed_noninterference  │
        │  budgeted_guarantee_voids_over_budget                       │
        └────────────────────────────────────────────────────────────┘
```

**Trusted (TCB), honestly enumerated:** rustc + LLVM; the tokio event loop and scheduler;
the network transport; the wall clock; the wire format / serialization (`dlc-protocol`,
CBOR); **and the proc-macro itself** (a macro that emits a wrong or vacuous obligation
would silently break the chain — §8, §9).

**Proven:** the pure transition core (`dlc_core::rsm`, Aeneas-verified with real bodies —
CLAUDE.md's in-crate reducer fence); the four guarantee classes; the R2 correspondence and
its `rust_*` transports — all **conditioned on the runtime returning `ok`** (partial
correctness; the ≥2³¹-node U32 depth overflow is excluded as physically unrealizable).

Acceptance for R6.1: `cargo run` two nodes; they converge on a shared register (G4),
observable in the logs.

---

## 6. The vertical slice (R6.3) — the killer demo

The ~30-line KV-ledger / replicated-register of §2.3, as a single demo crate, proving the
inflection from "proved a model" to "build systems this way." Exact scope:

1. **It runs.** `cargo run` boots two `Node<Ledger>` instances; a `credit` on one converges
   to the other (G4 convergence, transported by `rust_replicas_converge`). Crash-fault
   only — no Byzantine (BFT liveness is not done; roadmap §5).
2. **It rejects the three violations at compile time.** Three sibling fixtures, each a
   one-line perturbation of the good program, each failing to compile with the *named*
   diagnostic of §4 — wired as `trybuild`/compile-fail tests so "it rejects" is itself a
   green CI check:
   - `ledger_no_cap.rs` → `error[dlc_d::cap]` → routes to `rust_capability_safety`.
   - `ledger_leak.rs` → `error[dlc_d::flow]` → routes to `rust_distributed_noninterference`.
   - `ledger_over_budget.rs` → `error[dlc_d::budget]` → routes to
     `budgeted_guarantee_voids_over_budget`.
3. **The chain certifies the running node's envelope.** A `demo/ENVELOPE.md` (or a `make
   ledger` sub-entry) maps each attribute of the compiled `Ledger` to the transported
   theorem that certifies it: `Faults<1>` → budget void over 1; `Write@issuer` →
   `rust_capability_safety`; `χ ⊑ ℓ_low` → `rust_distributed_noninterference` — each with
   the `ok`/no-overflow fence stated.

Demo-scope open question (§9): single replicated register vs a real KV map; whether to
include the `declassify` read (which needs IFC-5, §8) or ship a pure-NI demo with no
downgrade.

---

## 7. Staging — each phase a checkable deliverable

| Phase | Deliverable | Checkable acceptance |
|-------|-------------|----------------------|
| **R6.0** (this) | this design + macro-expansion sketch; the surface, the 3 rejections, the routing fixed | doc merged; each rejection named against an existing theorem (§2–§4) |
| **R6.1** node | thin trusted tokio loop over `dlc_core::rsm::world_step`; TCB enumerated | `cargo run` two nodes converge on a register |
| **R6.2** surface + rejections | the `#[dlc_d::service]` / `#[write]` / `#[read]` proc-macro; Tier-1 encoding; Tier-2 obligation emission + discharge; the diagnostic layer | good program compiles; 3 compile-fail fixtures fail with the §4 named errors (trybuild) |
| **R6.3** demo | the ~30-line `Ledger`, runnable + the 3 fixtures + `ENVELOPE.md` chain | (1) runs+converges, (2) 3 rejections green as compile-fail tests, (3) envelope→theorem map complete |

Dependency note: R6.2's Tier-2 discharge depends on the transports (done) and on the
discharge-mechanism ruling (§9). IFC-5 (declassify) is only needed if R6.3 includes a
downgrade.

---

## 8. Honest gaps / hardest part

**Where "easy" is at risk.**
- **Tier-2 error re-rendering is the crux.** Tier-1 failures are rustc errors already; the
  danger is a Tier-2 obligation failure leaking a `PropDeriv`/Lean goal to the developer.
  Mapping a failed obligation back to its source span and declared bound, and rendering it
  as §4's diagnostics, is genuine, non-standard work — it is the single most likely place
  the "easy" claim breaks.

**Where "rigorous" is at risk.**
- **The macro↔verified-core linkage.** The proc-macro is TRUSTED (§5). A macro that emits
  the wrong obligation, or claims discharge without running the check, silently voids
  "compilation is the proof." Mitigations: (a) the Tier-2 check must *actually execute*
  against the governed theorems, not stub; (b) a golden-obligation test suite pinning what
  the macro emits for known-good/known-bad programs; (c) longer-term, verifying the macro
  (large, likely deferred).
- **Partial-correctness / U32 caveat.** The guarantee is conditioned on the runtime
  returning `ok` (no ≥2³¹-node overflow). This must surface *honestly* in the envelope
  claim ("exactly these bounded failure modes, provided the runtime returns ok"), not be
  hidden.
- **NI external-parameter caveat.** χ/ℓ are *supplied from the source type*, checked at
  compile time — not enforced on raw runtime bytes (the decode is impossible, and that
  impossibility is the design principle, not an apology). The developer must understand the
  label is a claim made in the type and checked at build time. This is honest and correct,
  but must be stated, or a reader may over-read "runtime IFC."
- **IFC-5 (sanctioned declassify) is unproven.** `Deriv.declassify` exists and its
  reduction is frozen-by-design (verifier-layer enforcement), and the NI bites already prove
  *unauthorized* declassify breaks `LowEquivG`; but the *delimited/relaxed-NI* theorem for
  *authorized* declassify is not yet proven (`r5-ifc-replan.md` IFC-5). Any service needing
  a downgrade (the demo's public read) has an unproven edge until IFC-5 lands.

**What is genuinely novel vs standard proc-macro work.** The proc-macro mechanics —
attribute parsing (`syn`), codegen (`quote`), compile-fail tests (`trybuild`) — are
standard, as is the phantom-label IFC-taint pattern (many Rust crates do type-level taint).
The novel part is that the emitted obligations discharge against a *machine-checked
distributed-systems metatheory transported to the deployed binary*: capability-safety, full
distributed noninterference, and type-level fault-budget voiding, each certified to the
running replicated node via the R2 correspondence. "The failure envelope is a type and
`cargo build` is the proof, to the metal" — no standard IFC/effect macro carries a checked
NI theorem down to a running replicated state machine.

---

## 9. OPEN QUESTIONS — for the author's ruling (not decided here)

1. **Front-end — confirm proc-macro over lark grammar?** §2.1 recommends the proc-macro
   decisively; the roadmap listed the grammar as the primary. Confirm the switch.
2. **Surface syntax: Unicode vs ASCII.** `flow = χ ⊑ ℓ_low` vs `flow = chi <= l_low`.
   Recommend ASCII canonical + Unicode sugar. Ruling?
3. **Label encoding.** Phantom const-generic labels + a `FlowsInto` trait vs a
   `Labeled<T, L>` wrapper vs associated types — how much type-level machinery before Tier-1
   ergonomics degrade? Which is the surface's canonical label carrier?
4. **Capability-token model.** Is `Cap<Write, Issuer>` a zero-size compile-time phantom
   (matches the Lean "proof not consumed at runtime" gate) or does it carry the Ed25519
   signed credential at runtime (matches `dlc-crypto`'s `Term.sign`)? The Lean models it as
   a compile-time gate; production authorization is a signed term.
5. **Tier-2 discharge mechanism (trust/speed).** Regenerate Lean + `lake build`? A
   RefinedRust check on the emitted shell? A lighter Rust-side certificate checker over the
   emitted obligation terms? This fixes both build latency and how much of §8's linkage risk
   is closed.
6. **How much to lean on RefinedRust (R3) for the shell NOW.** Ship R6.1/R6.3 with the async
   shell in the TCB (honest, fast) and treat R3 shell refinement as a later tightening
   (IFC-4 territory), or block R6.1 on the shell refinement existing (rigorous, slow)?
   Recommend shell-in-TCB now; confirm.
7. **Demo scope (R6.3).** Single replicated register vs a real KV map; include the
   `declassify` public read (needs IFC-5) or ship a pure-NI demo with no downgrade?
8. **Is the macro itself in the TCB, or do we commit to verifying it?** Recommend TCB + a
   golden-obligation test suite for R6; verifying the macro is a large later item. Confirm
   the boundary.

---

## 10. Fresh-2026 web searches a later pass should run

*(WebSearch budget exhausted this session — deferred. Run before writing the R6.2 macro and
before finalizing §4's diagnostic contract. Extends `r5-ifc-replan.md` §7.)*

1. `Rust proc-macro attribute custom compile error diagnostic span quality 2025 2026` —
   best practice for rustc-quality macro diagnostics (the §4 requirement).
2. `information flow control type system Rust macro compile-time 2025 2026` — IFC-2 surface
   prior art: how others compile a source-level flow annotation to a discharged obligation.
3. `session types / typestate Rust capability token zero-cost 2025 2026` — the `Cap<Write,
   Issuer>` Tier-1 encoding prior art (linear-capability-as-type in Rust).
4. `refinement type Rust compile-time obligation SMT discharge 2025 2026` — for the Tier-2
   discharge mechanism (§9 Q5); how Flux/Prusti/Creusot surface obligation failures.
5. `verified compiler macro trusted computing base proof-carrying code 2025 2026` — for the
   macro-in-TCB question (§9 Q8) and whether anyone verifies the surface→obligation compiler.
6. `delimited release noninterference Lean 4 2025 2026` — prior art for the IFC-5
   authorized-declassify statement the demo's public read needs.
7. `state machine replication information flow noninterference verified 2025 2026` — updates
   to seL4-IFC / FLAQR for the full-run transport framing behind the `flow` axis.
8. `label as type dependent classification runtime enforcement 2025 2026` — is "supply the
   label from the source type" (IFC-2's core) named/standard anywhere, to cite or contrast.
9. `trybuild compile-fail testing verified DSL macro 2025 2026` — for the R6.3 compile-fail
   fixture harness (the "it rejects the three violations" green check).
