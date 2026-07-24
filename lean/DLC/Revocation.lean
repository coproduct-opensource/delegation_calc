/-
# Revocation as a monotone time bound — the model, and the gap it exposes.

Phase 4 (spec/revocation-design.md). The agent-governance field's named gap: TTL-based expiry
fails at agent execution speed — an agent acts faster than a coarse TTL revokes, so a leaked/rogue
credential stays live for the whole TTL window ("short-lived credentials are necessary but not
sufficient", nhimg 2026). The research target is *fast* revocation (Heartbeat-Bound Hierarchical
Credentials, arXiv 2605.20704, names Tamarin/ProVerif mechanization as open).

DLC already ships the time machinery to model this: `TimeBound` (`DLC.Time`) and the `◇_τ`
modality `Prop'.within τ φ` with `within-I`/`within-E` (`DLC.Judgment`). A revocable says-credential
is `within validUntil (p says φ)`: it carries a validity bound, and acceptance is gated on
`now < validUntil` — the premise `within-E` defers to the `dlc-crypto` time anchor.

This file formalizes the **time-bound revocation model** — that revocation narrows the window
monotonically, is permanent, and leaves no post-revocation acceptance window (the property TTLs
lack) — and, as a pointed observation, that the CURRENT `within-E` strips the bound
*unconditionally*, so revocation is not YET a calculus-level guarantee. The fix (a
premise-carrying `within-E`, making an expired credential underivable) is the next increment;
this file is the model it will rest on.

## Fences
- **Model-level, over `TimeBound`.** These theorems are about the acceptance predicate; wiring the
  `now < τ` premise INTO `within-E` (so `Deriv` itself refuses an expired credential) is the next
  increment — see `current_withinE_ignores_time` for exactly what is not yet enforced.
- **Time-bound, not a revocation LIST.** This models expiry/short-TTL revocation (shrink the bound);
  an explicit JTI/blocklist (revoke a specific credential id before its natural expiry) is a distinct
  mechanism, not covered here.
- **Single time anchor.** No distributed-clock / anchor-freshness modelling (that is the
  `dlc-crypto::TimeAnchor` realization layer).
-/
import DLC.Judgment

namespace DLC

/-- A time-bounded credential is **acceptable** at `now` iff `now` strictly precedes its validity
bound `validUntil`. This is exactly the `now < τ` premise DLC's `within-E` defers to the
`dlc-crypto` time anchor (`Prop'.within validUntil (p says φ)` is the revocable credential). -/
def acceptableAt (validUntil now : TimeBound) : Prop := now.epochMs < validUntil.epochMs

instance (validUntil now : TimeBound) : Decidable (acceptableAt validUntil now) :=
  inferInstanceAs (Decidable (_ < _))

/-- **Revoke** a credential at epoch `revokeAt`: the effective validity bound becomes the EARLIER of
the original bound and the revocation time — revocation can only bring the bound forward. -/
def revoke (validUntil revokeAt : TimeBound) : TimeBound :=
  ⟨min validUntil.epochMs revokeAt.epochMs⟩

/-- **Revocation only narrows the window** (the temporal analogue of `attenuate_only_narrows`):
the revoked bound never exceeds the original. -/
theorem revoke_never_extends (v r : TimeBound) : (revoke v r).epochMs ≤ v.epochMs := by
  simp only [revoke]; omega

/-- **Revocation is permanent — no un-revocation.** Once a credential is unacceptable at `now`
(its bound has passed), it stays unacceptable at every later `now'`. Time only moves forward, so a
credential never comes back to life. -/
theorem revoked_stays_revoked (v now now' : TimeBound)
    (h : ¬ acceptableAt v now) (hle : now.epochMs ≤ now'.epochMs) :
    ¬ acceptableAt v now' := by
  simp only [acceptableAt] at *; omega

/-- **Revocation is effective — no post-revocation window.** After revoking at epoch `r`, the
credential is unacceptable at EVERY `now ≥ r`. This is the property TTLs lack: a coarse TTL leaves a
window up to the natural expiry, whereas revoking at `r` bounds acceptance at exactly `r` — the
"fast revocation" the field wants, as a theorem. -/
theorem revoke_bounds_acceptance (v r now : TimeBound)
    (h : r.epochMs ≤ now.epochMs) : ¬ acceptableAt (revoke v r) now := by
  simp only [acceptableAt, revoke]; omega

/-- Anti-vacuity (the predicate genuinely discriminates): a credential bounded at epoch 10 is
acceptable at 5 (before the bound)… -/
theorem acceptableAt_witness_valid : acceptableAt ⟨10⟩ ⟨5⟩ := by decide

/-- …and NOT acceptable at 10 (at/after the bound). So `acceptableAt` is two-sided, not a constant. -/
theorem acceptableAt_witness_expired : ¬ acceptableAt ⟨10⟩ ⟨10⟩ := by decide

/-- **The gap this design closes.** The CURRENT `within-E` strips the `◇_τ` bound UNCONDITIONALLY:
acceptance of `within τ φ` does not depend on `now` vs `τ` (the `now` here is unused). So the time
bound is decorative at the calculus level — the `now < τ` check lives only in `dlc-crypto`, and the
calculus alone offers no revocation guarantee. The next increment adds a premise-carrying `within-E`
requiring an `acceptableAt validUntil now` witness, after which an expired (revoked) credential —
having no such witness by `revoke_bounds_acceptance` — is underivable. -/
theorem current_withinE_ignores_time {Γ : Ctx} {M : Term} {τ : TimeBound} {φ : Prop'}
    (_now : TimeBound) (d : Deriv Γ M (Prop'.within τ φ)) : Nonempty (Deriv Γ M φ) :=
  ⟨Deriv.withinE Γ τ φ M d⟩

/-!
## `Deriv`-level revocation via a LAYERED acceptance judgment.

Rather than add a premise-carrying `within-E` constructor to `Deriv` (which would force every
function and proof over `Deriv` — `decideLean`, `reduce`, the correspondence/NI metatheory — to
handle the new case, with `sorryAx` risk on any missed match), we layer a **time-indexed acceptance
judgment ON TOP of `Deriv`**. This mirrors the trace-indexed `Auth(c, τ)` of DEKL 2.0
([arXiv 2604.22530]) and Etas's monitor-checked effect judgments ([arXiv 2607.17780]): the base
typing derivation is unchanged; acceptance is an outer relation indexed by the current time. It turns
the time-bound model above into a guarantee about *actual `Deriv`-typed credentials* without the
blast radius.
-/

/-- **Revocation-aware acceptance.** A credential `M` is ACCEPTED at time `now` iff it is a well-typed
`◇_τ`-bounded credential (`Γ ⊢ M : within τ φ`) AND `now` precedes its validity bound `τ`. The
`Deriv` component is the admission proof; `acceptableAt` is the revocation gate the current `within-E`
omits. (`φ` is the inner authority — for a says-credential, `Prop'.says p ψ`.) -/
def AcceptsRevocable (now : TimeBound) (Γ : Ctx) (M : Term) (τ : TimeBound) (φ : Prop') : Prop :=
  acceptableAt τ now ∧ Nonempty (Deriv Γ M (Prop'.within τ φ))

/-- **Revocation soundness (revoked ⟹ not accepted).** A credential whose bound has passed
(`¬ acceptableAt τ now`) is NOT accepted at `now`, no matter how well-typed it is — being a valid
`Deriv` is not enough once the horizon is crossed. This is the guarantee
`current_withinE_ignores_time` shows the bare calculus lacks. -/
theorem revoked_credential_not_accepted {Γ : Ctx} {M : Term} {τ : TimeBound} {φ : Prop'}
    (now : TimeBound) (hna : ¬ acceptableAt τ now) :
    ¬ AcceptsRevocable now Γ M τ φ := by
  intro h
  exact hna h.1

/-- After **revoking at epoch `r`**, the credential is not accepted at any `now ≥ r` — the model's
`revoke_bounds_acceptance` lifted to the `Deriv`-level acceptance judgment. -/
theorem revoked_at_not_accepted {Γ : Ctx} {M : Term} {v r : TimeBound} {φ : Prop'}
    (now : TimeBound) (h : r.epochMs ≤ now.epochMs) :
    ¬ AcceptsRevocable now Γ M (revoke v r) φ :=
  revoked_credential_not_accepted now (revoke_bounds_acceptance v r now h)

/-- **Acceptance is downward-closed in time.** If accepted at `now`, then accepted at any earlier
`now' ≤ now` — the same admission proof, still within the bound. (Together with
`revoked_credential_not_accepted`, acceptance is a single crossing at `τ`.) -/
theorem accepts_monotone_earlier {Γ : Ctx} {M : Term} {τ : TimeBound} {φ : Prop'}
    (now now' : TimeBound) (h : AcceptsRevocable now Γ M τ φ) (hle : now'.epochMs ≤ now.epochMs) :
    AcceptsRevocable now' Γ M τ φ := by
  obtain ⟨hacc, hd⟩ := h
  refine ⟨?_, hd⟩
  simp only [acceptableAt] at *; omega

/-- A concrete revocable credential term: a `◇_τ`-bounded says-affirmation
`withinIntro τ (sign p (now 0) sig)`. -/
def revocableCredential (p : Principal) (τ : TimeBound) : Term :=
  Term.withinIntro τ (Term.sign p (Term.now ⟨0⟩) ⟨0, []⟩)

/-- The real `Deriv` for the credential: `⊢ revocableCredential p τ : within τ (p says ⊤)`. -/
def revocableCredential_deriv (p : Principal) (τ : TimeBound) :
    Deriv Ctx.empty (revocableCredential p τ) (Prop'.within τ (Prop'.says p Prop'.top)) :=
  Deriv.withinI Ctx.empty τ (Prop'.says p Prop'.top)
    (Term.sign p (Term.now ⟨0⟩) ⟨0, []⟩)
    (Deriv.saysI Ctx.empty p Prop'.top (Term.now ⟨0⟩) ⟨0, []⟩ (Deriv.now [] ⟨0⟩))

/-- **Anti-vacuity (two-sided, over real `Deriv` terms).** The same well-typed credential (bound
`τ = 10`) IS accepted at `now = 5` (before the bound)… -/
theorem revocable_accepted_before_bound (p : Principal) :
    AcceptsRevocable ⟨5⟩ Ctx.empty (revocableCredential p ⟨10⟩) ⟨10⟩ (Prop'.says p Prop'.top) :=
  ⟨by decide, ⟨revocableCredential_deriv p ⟨10⟩⟩⟩

/-- …and is NOT accepted at `now = 10` (at/after the bound), even though the SAME `Deriv` exists — so
`AcceptsRevocable` is genuinely two-sided (a real credential rejected purely by the time gate), and
`revoked_credential_not_accepted` is not vacuous. -/
theorem revocable_not_accepted_at_bound (p : Principal) :
    ¬ AcceptsRevocable ⟨10⟩ Ctx.empty (revocableCredential p ⟨10⟩) ⟨10⟩ (Prop'.says p Prop'.top) :=
  revoked_credential_not_accepted ⟨10⟩ (by decide)

end DLC
