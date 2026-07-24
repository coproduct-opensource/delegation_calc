# Phase 4 — verified revocation: time-bounded `says` (design)

Status: **design + time-bound model + layered `Deriv`-level acceptance judgment landed**
(`lean/DLC/Revocation.lean`, §3). The deeper premise-carrying `within-E` constructor (making an expired
credential underivable in `Deriv` itself) is the later alternative. Design-first per repo discipline.

## 0. The gap (why this is a headline agent-governance need)

TTL-based expiry **fails at agent execution speed**. An autonomous agent issues actions faster than
a coarse TTL revokes, so a leaked or rogue credential stays live for the whole TTL window. The field
is explicit that *short-lived credentials are necessary but not sufficient* — the decisive control is
whether **revocation** holds under operational friction, not TTL alone:

- Short-lived credentials necessary-but-not-sufficient — nhimg.org, *"Short-lived credentials are
  necessary, but not sufficient for agents"* (2026).
- Fast revocation as the research target — **Heartbeat-Bound Hierarchical Credentials: Cryptographic
  Revocation for AI Agent Swarms**, `arxiv.org/html/2605.20704` (names Tamarin/ProVerif mechanization
  of the revocation protocol as an **open** direction — exactly DLC's lane).
- Revocation-service blocklists (JTI tracking, invalidate before natural expiry) —
  `techinterview.org/post/3233469926/lld-token-revocation`.
- Token-lifetime trade-offs / epoch timestamps — gitguardian, guptadeepak CIAM (2026).

DLC-D carries every other admission-control guarantee to deployed Rust but **does not model
revocation** — the plan's named Phase-4 gap.

## 1. The DLC mechanism — a revocable credential is a time-bounded `says`

DLC already ships the machinery, so revocation needs **no new syntax**:

- `TimeBound { epochMs : Nat }` (`DLC.Time`) — a validity horizon.
- `Prop'.within τ φ` — the `◇_τ` modality: "φ, valid while `now < τ`" — with `within-I` (pair φ with a
  time proof) and `within-E` (strip it, the verifier checking `now < τ` at elimination).

**A revocable says-credential is `within validUntil (p says φ)`**: the issuer binds the affirmation to
a validity horizon. Acceptance is gated on `now < validUntil` — modelled by

    acceptableAt validUntil now  :=  now.epochMs < validUntil.epochMs      -- Revocation.lean

**Revocation = bringing the horizon forward**: `revoke validUntil revokeAt := ⟨min validUntil revokeAt⟩`
— the effective bound becomes the earlier of the natural expiry and the revocation epoch. This is the
short-TTL/expiry form of revocation (a heartbeat that must re-issue, à la arXiv 2605.20704); an
explicit JTI/blocklist is a distinct mechanism (§4 fence).

## 2. What is proven now (`lean/DLC/Revocation.lean`, axiom set `[propext, Quot.sound]`)

The **revocation semantics**, as the temporal analogue of the attenuation-narrowing cluster:

- `revoke_never_extends` — revocation only NARROWS the window (`revoke v r ≤ v`); the temporal twin of
  `attenuate_only_narrows`. You can never widen a credential's validity by "revoking".
- `revoked_stays_revoked` — revocation is **permanent**: once unacceptable at `now`, unacceptable at
  every later `now'` (time moves forward; no un-revocation).
- `revoke_bounds_acceptance` — revocation is **effective / leaves no window**: after revoking at `r`,
  the credential is unacceptable at *every* `now ≥ r`. This is precisely the property TTLs lack (a TTL
  leaves a window up to the natural expiry) — "fast revocation" as a theorem.
- `acceptableAt_witness_valid` / `_expired` — anti-vacuity: the predicate genuinely discriminates
  (acceptable at 5, not at 10, for bound 10).

## 3. `Deriv`-level enforcement — a LAYERED acceptance judgment (LANDED)

`Revocation.lean`'s `current_withinE_ignores_time` records the **honest gap**: the CURRENT `within-E`
strips `◇_τ` **unconditionally** — acceptance of `within τ φ` does not depend on `now` vs `τ`. So at
the bare-calculus level the time bound is decorative; the `now < τ` check lives only in `dlc-crypto`.

Rather than add a premise-carrying `within-E` **constructor** to `Deriv` — which would force every
function/proof over `Deriv` (`decideLean`, `reduce`, the correspondence/NI metatheory) to handle the
new case, with `sorryAx` risk on any missed match — we layer a **time-indexed acceptance judgment ON
TOP of `Deriv`** (the trace-indexed `Auth(c,τ)` of DEKL 2.0 `arxiv.org/pdf/2604.22530`; Etas's
monitor-checked effect judgments `arxiv.org/html/2607.17780`). The base typing is unchanged;
acceptance is an outer relation indexed by the current time:

    AcceptsRevocable now Γ M τ φ  :=  acceptableAt τ now  ∧  Nonempty (Deriv Γ M (within τ φ))

Proven (`Revocation.lean`, axioms ⊆ `[propext, Quot.sound]`):

- `revoked_credential_not_accepted` — **revocation soundness**: `¬ acceptableAt τ now →
  ¬ AcceptsRevocable now Γ M τ φ`; a credential past its bound is not accepted however well-typed.
- `revoked_at_not_accepted` — after revoking at `r`, not accepted at any `now ≥ r` (the model's
  `revoke_bounds_acceptance` lifted to the `Deriv` judgment).
- `accepts_monotone_earlier` — acceptance is downward-closed in time (a single crossing at `τ`).
- `revocableCredential_deriv` + `revocable_accepted_before_bound` / `revocable_not_accepted_at_bound`
  — a REAL `Deriv` credential `⊢ withinIntro τ (sign p (now 0) σ) : within τ (p says ⊤)`, accepted at
  `now=5` and rejected at `now=10` (bound 10): two-sided over an actual derivation, so the judgment is
  inhabited and the soundness theorem non-vacuous.

**Deeper alternative (later):** the premise-carrying `within-E` constructor makes an expired credential
*underivable* in `Deriv` itself (not merely un-accepted by the outer judgment) — stronger, but requires
the full metatheory sweep (every `Deriv` consumer updated). The layered judgment delivers the guarantee
now without that blast radius. A Tamarin/ProVerif revocation model (the arXiv 2605.20704 open item)
mirrors it at the protocol layer.

## 4. Honest fences

- **Layered, not intrinsic.** §3's `AcceptsRevocable` is an outer judgment; making an expired
  credential *underivable in `Deriv` itself* (the premise-carrying `within-E` constructor) is the
  deeper, later alternative — `current_withinE_ignores_time` marks what the bare calculus still omits.
- **Time-bound expiry, not a revocation LIST.** This is shrink-the-horizon revocation; an explicit
  per-credential JTI/blocklist (revoke one id before its natural expiry) is a separate mechanism.
- **Single time anchor.** No distributed-clock / anchor-freshness modelling — that is the
  `dlc-crypto::TimeAnchor` realization layer (opaque to the calculus).
- **Single-decree, safety-not-liveness**, like the rest of the transport chain until BFT liveness.

## 5. Protocol-layer mechanization (Tamarin) — LANDED

`models/tamarin/dlcd-revocation.spthy` (companion `dlcd-revocation-bite.spthy`) mechanizes the
revocation protocol under Dolev–Yao — the arXiv 2605.20704 open item, mirroring the house style of
`dlcd-interop.spthy` (tamarin-prover 1.12.0, CI-gated in `tamarin.yml`). Epoch = trace ordering
(`#r < #a`); revocation = an issuer-published `Revoked(I, cid)` action; the verifier consults the
revocation list via the `RevocationCheck` restriction (accept only if no earlier revocation).

Lemmas — **all verified**: `accept_binds_issuer` (forgery-resistance: acceptance ⟹ genuine issuance
unless the key is revealed), `accept_not_revoked` (**revocation soundness**: an accepted credential
was not revoked before acceptance — the protocol twin of `Revocation.lean`'s
`revoked_credential_not_accepted`), `revoke_is_permanent` (once revoked, any acceptance strictly
precedes the revocation — no un-revocation), `exec_accept` (anti-vacuity: an honest issue+accept with
no key revealed is reachable). The differential **BITE** (`dlcd-revocation-bite.spthy` +
`scripts/check-tamarin-revocation-bite.sh`, CI-gated): with `RevocationCheck` removed,
`revoked_replay_reachable` (post-revocation replay) is VERIFIED (reachable), while the same lemma is
FALSIFIED in the guarded model — the machine-checked statement that the revocation check is
load-bearing.

**ProVerif cross-check LANDED** (`models/proverif/dlcd-revocation.pv`, CI-gated in `proverif.yml`):
an independent applied-pi/Horn-clause engine AGREES on the two properties in its reach —
`accept_binds_issuer` (forgery-resistance correspondence, `is true`, scoped to honest issuers) and
reachability (`Accepted` reachable, anti-vacuity). Honest division of labour, stated in the `.pv`
header: the TEMPORAL revocation core (`accept_not_revoked` / `revoke_is_permanent` — a negation over
event ordering) is **Tamarin-only**, since ProVerif's monotonic Horn translation cannot express "no
`Revoked` precedes `Accepted`" (injective correspondence gives "there IS an earlier event", not "there
is NONE") — the same honest projection as the interop disequality and replication slot-agreement
fences. Revocation is now verified across four layers: Lean model + `Deriv` judgment + Tamarin + ProVerif.
