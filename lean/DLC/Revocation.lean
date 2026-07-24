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

end DLC
