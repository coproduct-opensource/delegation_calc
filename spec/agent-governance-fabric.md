# DLC-D as the verified admission-control kernel for a multi-agent governance fabric

*Positioning memo. 2026-07-24. Branch `dlc-d/phase0-carve`. Companion to
`spec/r6-1b-replication-protocol.md` (the runtime), `spec/dlc-d-roadmap.md`, and the R6.2
reframe `spec/r6.2-agent-service-envelope.md` (forthcoming). This memo stakes a claim; every
row of every table below cites a machine-checked theorem by name or is marked as an honest gap.*

---

## 0. Thesis

The 2025–2026 multi-agent-AI-governance literature is independently converging on a small set of
primitives — a cryptographic **admission check** before an agent action mutates state, **attenuated
multi-hop delegation**, an **append-only provenance chain**, and **Byzantine-tolerant agreement**
on agent decisions. These are being built as engineering artifacts, validated by bounded
model-checking or empirical attack suites, **not by proof**.

DLC-D already *is* the proved version of that primitive set. Its `commit-I` typing rule is the
Abadi / Garg–Pfenning authorization logic (`says`) those token schemes are informal cousins of; its
guarantees are machine-checked in Lean and **transported to deployed Rust** via Aeneas. So the
claim is narrow and defensible:

> **DLC-D is a verified admission-control + Byzantine-agreement kernel** — the formal-proof answer
> to the admission-control protocols the agent-governance field is now standardising, carried down
> to running code rather than stopping at a model.

This is not a claim that DLC-D is a complete agent runtime (it is not — §5 is the honest gap list).
It is a claim about the *kernel*: the part where "who may act, and do honest nodes agree even under
a Byzantine minority" is decided, and where a bug is catastrophic.

---

## 1. What the field is building (2025–2026), and with what evidence

| System | What it is | Strongest evidence it offers |
|---|---|---|
| **Agent Control Protocol** (ACP, arXiv 2603.18829, v1.14→v1.30) | "the admission-control layer between agent intent and system state mutation; before any action executes it must pass a cryptographic admission check validating identity, capability scope, delegation chain, and policy compliance *simultaneously*" | a **TLA+ model, 3 invariants, TLC-runnable** (bounded model-check) |
| **Invocation-Bound Capability Tokens** (IBCT, Prakash 2026) | identity + attenuated authorization + provenance in an **append-only token chain**; Biscuit / JWT wire | **empirical: "100% rejection across 600 attack attempts"** |
| **PAuth** (Sharma 2026) | task-scoped "envelopes" binding operands to symbolic provenance ("NL slices") | design + reference impl |
| **MCP OAuth** (Anthropic/Arcade/Microsoft/Okta) | RFC 8707 audience binding + RFC 8693 token exchange for delegation | a standard / spec |
| **Biscuit** (eclipse-biscuit) | append-only signed blocks + Datalog checks, offline verification | spec + widely-deployed impl |
| **Byzantine multi-agent consensus** (e.g. arXiv 2605.09076) | confidence-weighted BFT for LLM-agent decisions | protocols + experiments |

Two observations set up the entire positioning:

1. **The strongest formal evidence anyone offers is a bounded model-check (ACP's TLA+) or an
   empirical attack suite (IBCT's 600 attacks).** A model-check explores a finite state space; an
   attack suite covers the attacks you thought of. Neither is a proof over all executions and all
   adversaries, and neither is carried to the deployed code.
2. **ACP names its own open failure mode: "deviation collapse — enforcement active but never
   exercised because upstream constraints eliminate the conditions required for DENIED decisions."**
   That is precisely a *vacuity* bug: a gate that is green because it never fires. DLC-D's entire
   verification discipline is built to prevent exactly this (§4).

---

## 2. The mapping — each requirement to a machine-checked mechanism

| Agent-governance requirement | DLC-D mechanism (theorem / construct) | Where | Proof status |
|---|---|---|---|
| Only an authorized principal may invoke a tool / write | `capability_safety` (every logged command was `says`-authorized) + `commit-I` typing rule (`Deriv.commitI`) + runtime forgery-resistance `verify_qc` | `lean/DLCD/CapSafety.lean`, `lean/DLC/Judgment.lean`, `crates/dlc-d-node/src/proto.rs` | **proved** |
| …carried to the *deployed* engine | `rust_capability_safety` (the transported corollary) | `lean/DLCD/Transport.lean` | **proved (partial-correctness)** |
| Agreement on decisions under a Byzantine minority | `rust_byz_agreement` (two `2f+1`-of-`3f+1` certificates certify the same value) | `lean/DLCD/TransportConsensus.lean` | **proved (safety)** |
| Append-only provenance / audit chain | `WellFormedLog` (inductive provenance for the committed log) | `lean/DLCD/CapSafety.lean` | **proved** |
| Cross-agent / cross-tenant data isolation | `distributed_noninterference` (a low observer cannot distinguish differing high stores) | `lean/DLCD/DistributedNI.lean` | **proved at the model / decoded-type level** |
| A total order on agent operations | `single_linearization` | `lean/DLCD/Linearizable.lean` | **proved** |
| A declared, enforced failure envelope | `budgeted_guarantee_voids_over_budget` (behaviour is *uninhabited* over budget) | `lean/DLCD/FaultGrade.lean` | **proved (type-level)** |
| Multi-hop delegation with attenuation (narrows only) | `attenuate_only_narrows` (a well-typed attenuation carries its parent authority + the narrowing witness `φ ⊢ ψ`) + `attenuate_chain_narrows` (leaf authority entailed by the root over a chain) | `lean/DLC/AttenuateNarrows.lean` | **proved** (`[propext]`; the Tamarin `attenuation_roots_in_issuance` structural assumption discharged) |
| Enforcement is actually exercised (no deviation collapse) | anti-vacuity witnesses + right-reason bites + the differential bite gate | throughout `lean/DLCD/*`, `models/tamarin/*`, `scripts/check-tamarin-bite.sh` | **methodology, applied** (§4) |
| Revocation faster than agent execution | time-bounded `says` (`within validUntil (p says φ)`): `revoke_bounds_acceptance` / `revoked_credential_not_accepted` (revoked ⟹ not accepted) + Tamarin `accept_not_revoked` + real expiring Biscuit (`authorize_at`) | `lean/DLC/Revocation.lean`, `models/tamarin/dlcd-revocation.spthy`, `models/proverif/dlcd-revocation.pv`, `crates/dlc-interop/src/biscuit.rs` | **proved + verified across 5 layers** (Lean + Deriv judgment + Tamarin + ProVerif + Biscuit wire; the arXiv 2605.20704 open item) |
| Progress under a faulty leader (BFT liveness) | view-change bounded-liveness: progress reachable past a silent leader (`dlcd-viewchange.spthy`) AND past a **Byzantine equivocating** leader (`dlcd-viewchange-byz.spthy`, n=4 quorum 3) + `no_two_decisions` / `double_vote_needs_reveal` (agreement + anti-equivocation survive) | `spec/bft-liveness-design.md`, `models/tamarin/dlcd-viewchange{,-byz}.spthy` | **designed + BOUNDED** (Tamarin exists-trace, crash & Byzantine leader; full temporal ◇ needs TLA+, §5) |

"Proved" here means: a Lean theorem with a `[propext, Classical.choice, Quot.sound]` axiom
footprint (no `sorry`/`native_decide`), governed by a pinned `expected-axioms` snapshot, with a
non-vacuous witness. The `rust_*` rows additionally carry the theorem to the Aeneas-translated Rust
under the honest partial-correctness condition (the bounded reducer returns `ok`).

---

## 3. The benchmark — on proof strength

The axis that matters for a *governance kernel* is not throughput or features; it is **how much of
the behaviour space the safety argument actually covers**.

| | admission-control safety | agreement under Byzantine faults | carried to deployed code | over-all-adversaries |
|---|---|---|---|---|
| **ACP** | TLA+ model-check (bounded) | not the focus | no (model only) | no (finite states) |
| **IBCT** | empirical (600 attacks) | no | reference impl | no (tested attacks) |
| **PAuth / MCP / Biscuit** | design / spec / Datalog checks | no | impl | no |
| **Byzantine multi-agent** | — | protocol + experiments | no | no |
| **DLC-D** | `capability_safety`, machine-checked | `rust_byz_agreement`, machine-checked | **yes** (`rust_*`, partial-correctness) | **yes** (Lean over all executions; Tamarin/ProVerif over all Dolev-Yao adversaries) |

The concrete contrast to draw in any external writeup: *ACP model-checks 3 invariants over a finite
state space; DLC-D compiles the proof and carries it to deployed Rust. IBCT rejects 600 attacks it
tried; DLC-D's replication protocol is proved to reject every Dolev-Yao adversary* (Tamarin +
ProVerif, `models/tamarin/dlcd-replication.spthy`, `models/proverif/dlcd-replication.pv`),
*with the certificate-forgery class* (the Nethermind XDC bug) *closed by construction and the
equivocation boundary made explicit* (`rust_byz_agreement`; `spec/r6-1b-replication-protocol.md`
§6.4–6.5).

---

## 4. The deviation-collapse answer (why DLC-D's methodology matters here)

ACP's named open problem — enforcement that is active but never exercised — is the failure DLC-D's
discipline is *specifically* built to catch, and has caught repeatedly in this program:

- **Anti-vacuity witnesses.** Every guarantee is paired with a concrete run that inhabits its
  premise (e.g. `byz_decided_witness`, the slice witness `dlc_d_slice_witness`). A guarantee that
  could never fire would have no witness and would not be accepted.
- **Right-reason bites.** Every load-bearing restriction is paired with a proof that *removing it
  breaks something*, at the expected place for the expected reason (e.g. the replication model's
  differential bite: deleting the one-vote-per-slot guard makes disagreement reachable with no key
  compromise, and `scripts/check-tamarin-bite.sh` gates that the *same* attack is falsified in the
  guarded model).
- **The equivocation correction.** When this program's own "Byzantine-leader-tolerant" claim was
  overstated, writing the adversary down refuted it and forced the honest scope
  (`crates/dlc-d-node/tests/byzantine.rs`; `spec/r6-1b-replication-protocol.md` §6.4). A gate that
  is green for the wrong reason is treated as a defect, not a pass.

So DLC-D does not merely *avoid* deviation collapse — it has a reusable, machine-checked method for
proving a gate is exercised. That method is directly transferable to an ACP-style admission layer.

---

## 5. Honest gap list (what this kernel is *not*, yet)

- **Single-decree, single-round.** The runtime governs one decision stream at a time; multi-slot
  log-matching (`log_agreement`) is model-level only, with no runtime multi-slot decision function.
- **Liveness is DESIGNED + BOUNDED, not a full temporal proof.** `rust_byz_agreement` remains
  agreement (safety). A view-change *design* (`spec/bft-liveness-design.md`) + a *bounded* Tamarin
  artifacts now exist for BOTH a crash/silent leader (`dlcd-viewchange.spthy`) and a **Byzantine
  equivocating** leader (`dlcd-viewchange-byz.spthy`, n=4 quorum 3): progress is *reachable* past the
  faulty leader via rotation, agreement + anti-equivocation survive. The full temporal ◇ ("always
  eventually decides") needs a fair-scheduling model-checker (TLA+/TLC) this no-Mathlib Lean toolchain
  lacks — FLP forces the synchrony assumption, which DLC-D states explicitly (unlike ACP's
  assumption-free TLA+ check). Remaining: TLA+/TLC ◇ liveness; the tight f=1 Byzantine safety bound
  (f+1 reveals, fenced — a Tamarin disequality limit); multi-decree Byzantine lift.
- **`attenuate` converse — CLOSED.** `attenuate_only_narrows` proves a typed attenuation *carries* the
  narrowing witness; the converse (a genuine *widening* is *underivable*) is now proved too
  (`lean/DLC/DerivSound.lean`, `[propext]`): a boolean valuation model + full soundness `deriv_sound`
  (all 31 constructors) gives `widening_says_underivable` / `attenuate_cannot_widen`. The model is the
  program's first NEGATIVE-direction engine (underivability from a falsifying valuation) — it also
  under-writes the Deriv-level revocation bite.
- **Runtime IFC is type-level.** A faithful runtime label-decode was shown *impossible* (finite
  hand lattice vs unbounded runtime labels); the `flow` axis is a compile-time claim checked at
  build, not runtime label-byte enforcement. This is a design principle, not an apology, but it
  must be stated.
- **Compile-time `says` ↔ runtime token bridge is unbuilt.** DLC-D's capability is a typed
  `says`-credential; production agent auth is a runtime signed token (Biscuit / JWT). The bridge
  exists in pieces (`dlc-crypto::signed_term::verify_in_keyring` realizes the `says`-signature
  check) but the wire correspondence is the interop deliverable (§6), not yet done.
- **Attenuation soundness is unproven.** `Term::Attenuate` / `Delegate` / `SpeaksFor` exist; the
  metatheorem "attenuation only narrows authority" over `Deriv` does not.
- **Revocation is not modelled.** The field's named gap (TTL-based revocation fails at agent
  execution speed) is not addressed; revocable / epoch'd `says` is new metatheory.
- **Partial-correctness condition rides along** on every `rust_*` transport (holds when the bounded
  reducer returns `ok`).

---

## 6. The interop story (the bridge — BUILT)

The field has already picked its wire: **Biscuit** (append-only signed blocks) for multi-hop
delegation, **RFC 8693** token exchange for delegation hops, **RFC 8707** audience binding for
scoping, under the **MCP OAuth** umbrella. DLC-D's constructs map onto these directly:

| DLC-D | Interop counterpart |
|---|---|
| `says`-credential (`Sign`/`Verify` + Ed25519, `verify_in_keyring`) | a Biscuit block / signed JWT |
| `Delegate` / `Attenuate` / `SpeaksFor` | Biscuit attenuation / RFC 8693 token exchange |
| `WellFormedLog` (append-only committed log) | IBCT's append-only token chain / audit provenance |
| a command's sink / IFC label | MCP RFC 8707 audience binding |

The bridge is **built**: `spec/interop-says-biscuit.md`, a Tamarin/ProVerif-modelled protocol
(`dlcd-interop.spthy` + differential bite + `dlcd-interop.pv`), and the `dlc-interop` crate — which
now encodes a `says`-credential into a **genuine `biscuit-auth` v6 token** (`to_biscuit`/`from_biscuit`,
the credential riding as a Datalog fact in a real Ed25519-block-chained Biscuit) reusing
`dlc-protocol::wire` verbatim, with the revocation gate realized on the wire as a Biscuit
`check if dlc_now($t), $t <= validUntil` expiry (`to_biscuit_with_expiry`/`authorize_at`). The
`biscuit-auth` dependency is confined to `dlc-interop` — `dlc-core` stays Aeneas-translatable (the
fence). A DLC-D-governed service now *interoperates* with the emerging standard instead of being a
parallel island — the same "reuse the encoder, add a framing layer, model before wire" discipline.

---

## 7. The shape of the claim, stated for external use

> A DLC-D agent service declares its authority envelope — who may invoke which tool, how information
> may flow, and how many faults it tolerates — as a **type**. `cargo build` green means the deployed
> binary's admission control is **machine-checked**, honest nodes **agree even under a Byzantine
> minority**, and the enforcement is **provably exercised**. Where the leading protocols offer a
> bounded model-check or an attack suite, DLC-D offers a proof carried to the running code — with
> multi-hop **attenuation narrowing proved**, **revocation** mechanized across five layers (Lean →
> Deriv → Tamarin → ProVerif → real Biscuit wire), and **BFT liveness designed + bounded-checked** —
> and is honest about exactly where the proof stops (single-decree, liveness bounded-not-temporal,
> type-level flow — with the `attenuate` converse now closed via a boolean model of `Deriv`).

That envelope-as-a-type surface is R6.2, reframed as the agent authority-envelope
(`spec/r6.2-agent-service-envelope.md`); the runnable governed service is R6.3.

---

## 8. Prior art (URLs recorded per program discipline)

- Agent Control Protocol — arXiv:2603.18829 (admission control; TLA+ model; "deviation collapse").
- Atomic Decision Boundaries — arXiv:2604.17511 (execution-time admissibility).
- Authorization Propagation in Multi-Agent AI Systems — arXiv:2605.05440 (IBCT; identity governance).
- Robust Multi-Agent LLMs under Byzantine Faults — arXiv:2605.09076.
- Vouchsafe: zero-infrastructure capability graph — arXiv:2601.02254.
- Garg–Pfenning / Abadi authorization logic (`says`) — cs.cmu.edu/~fp/papers/affknow06.pdf.
- POLARIS cross-domain access control — arXiv:2511.22017.
- Biscuit specification — github.com/eclipse-biscuit/biscuit; RFC 8693 (token exchange), RFC 8707
  (resource indicators); MCP OAuth authorization spec.
