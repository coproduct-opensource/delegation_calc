# Phase 4 — verified revocation: time-bounded `says` (design)

Status: **design + time-bound model landed** (`lean/DLC/Revocation.lean`); the `Deriv`-level
enforcement (a premise-carrying `within-E`) is the next increment. Design-first per repo discipline.

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

## 3. The metatheorem to prove NEXT (the `Deriv`-level enforcement)

`Revocation.lean`'s `current_withinE_ignores_time` records the **honest gap**: the CURRENT `within-E`
strips `◇_τ` **unconditionally** — acceptance of `within τ φ` does not depend on `now` vs `τ`. So at
the calculus level the time bound is decorative; the `now < τ` check lives only in `dlc-crypto`.

Next increment: add a premise-carrying elimination

    within-E-anchored  (d : Deriv Γ M (within τ φ)) (anchor : acceptableAt τ now)  :  Deriv Γ M φ

and prove **revocation soundness**: a revoked/expired credential (`now ≥ revoke validUntil r`, hence
no `acceptableAt` witness by `revoke_bounds_acceptance`) is **not eliminable** — no acceptance
derivation exists. This turns the model theorems above into a guarantee about `Deriv` itself, and is
the DLC analogue of the arXiv 2605.20704 revocation protocol, carried to the typed calculus. Then a
Tamarin/ProVerif model (the field's open item) mirrors it at the protocol layer.

## 4. Honest fences

- **Model-level today.** §2 is over the `acceptableAt` predicate; §3 (wiring the premise into `Deriv`)
  is the next increment — `current_withinE_ignores_time` marks exactly what is not yet enforced.
- **Time-bound expiry, not a revocation LIST.** This is shrink-the-horizon revocation; an explicit
  per-credential JTI/blocklist (revoke one id before its natural expiry) is a separate mechanism.
- **Single time anchor.** No distributed-clock / anchor-freshness modelling — that is the
  `dlc-crypto::TimeAnchor` realization layer (opaque to the calculus).
- **Single-decree, safety-not-liveness**, like the rest of the transport chain until BFT liveness.
