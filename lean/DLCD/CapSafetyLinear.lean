import DLCD.CapSafety
import DLC.CarveJudgment

/-! # DLC-D 2.c — the linear capability credential as a SEALED judgment `CDerivS`

This module supplies the **linear** capability layer that mirrors the additive
`DLCD.CapSafety` layer, but over the DILL-sound CARVe judgment `CDeriv`
(`DLC.CarveJudgment`) instead of the additive `DLC.Deriv`. The controlled
operation (committing a write) is gated behind a proof that the issuing
principal `says` the guarding capability — where that `says`-proof is now a
**linear** signed credential built on `CDeriv`'s resource-vector contexts.

## Why a SEAL over `CDeriv`, not a `CDeriv` constructor (the modality-mismatch)

`CDeriv` deliberately has **no `says`-introduction**. Adding a `saysI` *directly*
to `CDeriv` is INFEASIBLE — and the obstruction is a MODALITY mismatch, not a
resource-accounting one:

* `CDeriv.saysE` (`DLC/CarveJudgment.lean:420`) concludes `Prop'.says p ψ` —
  it KEEPS the modality.
* but the operational rule `step (saysBind p (sign p' m _) N) = subst N m : ψ`
  (`DLC/Reduce.lean:90-96`) STRIPS the modality.

These are consistent only while `says` is *uninhabited* in `CDeriv`: the
`saysE` β-branch of subject reduction (`CarveJudgment.lean:2236-2246`) is
currently VACUOUS. A `CDeriv.saysI` would make that redex reachable and
untypable at `says p ψ`, breaking `cderiv_subject_reduction'`.

The corroboration is in DLC's own `PropDeriv`, which *does* carry a `saysI`
precisely because it OMITS the modality-keeping `saysE` (it keeps only the
stripping `letSaysE`/`delegate`). So the sound fix is a **separate sealed
judgment** `CDerivS` layered *on top of* `CDeriv`, leaving `CDeriv` — and its
subject-reduction / progress theorems — entirely untouched. `CDerivS.embed`
lifts any `CDeriv` derivation; `CDerivS.saysI` adds the (linear) signed
affirmation intro that `CDeriv` cannot host. The seal never feeds back into
`CDeriv`, so no `CDeriv` metatheorem is perturbed (this file adds NOTHING to
`CarveJudgment`).

## Resource discipline of the seal

`CDerivS.saysI` passes the context `Γ` through UNCHANGED — the credential
consumes exactly its subject's resources and nothing more. This mirrors
`DLC.Deriv.saysI` and `PropDeriv.saysI`, which likewise do not consume beyond
the underlying subject derivation. So a linear (`Mult.one`) subject stays
linear under the seal: the credential is genuinely resource-correct.

## Non-circular capability-safety

`WellFormedLogL` is an inductive PROVENANCE predicate (empty log, or an
`AuthorizedL` commit onto a well-formed log), NOT "every command is
authorized". `capability_safety_linear` EXTRACTS per-command authorization by
induction over that provenance — the linear-layer twin of
`DLCD.capability_safety`.

## The additive ↔ linear bridge — HONESTLY DEFERRED

At the *credential shape* level `CDerivS.saysI` mirrors `Deriv.saysI` exactly
(same `Principal`/`Signature` carrier, same `says`-conclusion), so the two
layers' signed credentials correspond one-for-one. A *functorial* embedding
`Deriv _ _ φ → CDeriv _ _ φ` (hence `Deriv → CDerivS`) would require the full
`Deriv`→CARVe judgment migration + its substitution-preservation lemma (the
open L4 line — see `CarveJudgment`'s Wood–Atkey references); that translation is
NOT yet complete, so the bridge is stated as future work rather than proved.
The linear layer here stands on its own `CDeriv`-native witness.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Garg & Pfenning, *Non-Interference in Constructive Authorization Logic*
  (CSFW 2006): the constructive `says` affirmation modality built as a MODAL
  ENRICHMENT OF LINEAR LOGIC precisely to model *consumable* authorizations —
  the theoretical warrant for a linear says-credential.
  https://people.mpi-sws.org/~dg/papers/csfw06.pdf
- Bowers, Bauer, Garg, Pfenning & Reiter, *Consumable Credentials in
  Linear-Logic-Based Access-Control Systems* (NDSS 2007): credentials with
  use-bounded (linear) semantics in an access-control logic — the
  single-use/linear reading the RSM `cap` slot foreshadows.
  http://users.ece.cmu.edu/~lbauer/papers/2007/ndss2007-consumable.pdf ,
  https://www.ndss-symposium.org/ndss2007/consumable-credentials-linear-logic-based-access-control-systems/
- Garg, Bauer, Bowers, Pfenning & Reiter, *A Linear Logic of Authorization and
  Knowledge* (ESORICS 2006): the linear authorization logic these build on.
  https://link.springer.com/chapter/10.1007/11863908_19
- (additive-layer anchors, carried over) Abadi et al., *A Core Calculus of
  Dependency* (POPL 1999) — `says` as a principal-indexed monad;
  Bauer, *Access Control for the Web via Proof-Carrying Authorization* — the
  monitor-checks-a-proof discipline.
-/

namespace DLCD

open DLC
open DLC.Carve (Mult)

/-! ## 1. The sealed judgment `CDerivS` (option A).

`CDerivS` is a SEAL over `CDeriv`: `embed` lifts any CARVe derivation, and
`saysI` adds the linear signed-affirmation introduction that `CDeriv` cannot
host (modality mismatch, above). It is a `Prop` — we only ever assert its
INHABITATION (via `Nonempty`), never eliminate it into data. -/

/-- **The linear says-credential seal.** Two constructors:
* `embed` — lift any `CDeriv Γ M φ` unchanged (the sealed judgment is a genuine
  extension of the CARVe judgment);
* `saysI` — from a sealed derivation of `φ` under `Γ`, conclude
  `issuer says φ` for the signed term `Term.sign issuer M sig`, passing `Γ`
  through UNCHANGED (consumes exactly the subject's resources — the
  resource-correct discipline, mirroring `DLC.Deriv.saysI`). The
  `Principal`/`Signature` carriers are exactly those of `DLC.Deriv.saysI`. -/
inductive CDerivS : Carve.Ctx Prop' → Term → Prop' → Prop where
  /-- Lift any CARVe derivation into the seal. -/
  | embed {Γ : Carve.Ctx Prop'} {M : Term} {φ : Prop'} :
      CDeriv Γ M φ → CDerivS Γ M φ
  /-- The linear signed-affirmation introduction `CDeriv` cannot host. `Γ`
  passes through unchanged. -/
  | saysI {Γ : Carve.Ctx Prop'} {M : Term} {φ : Prop'}
      (issuer : Principal) (sig : Signature) :
      CDerivS Γ M φ → CDerivS Γ (Term.sign issuer M sig) (Prop'.says issuer φ)

/-! ## 2. The linear authorization predicate.

Same shape as `DLCD.Authorized`, but the witness is a `CDerivS` (linear)
credential rather than a `Deriv` (additive) one. -/

/-- **Linear proof-carrying authorization.** `c` is authorized by `issuer` iff
its guarding capability is `issuer says capProp` AND a real `CDerivS` witness of
`issuer says capProp` exists. `Nonempty` erases the specific witness to a `Prop`
while preserving its existence. -/
def AuthorizedL (c : Command) (issuer : Principal) : Prop :=
  ∃ (Γ : Carve.Ctx Prop') (capTerm : Term) (capProp : Prop'),
    c.cap = some (Prop'.says issuer capProp) ∧
    Nonempty (CDerivS Γ capTerm (Prop'.says issuer capProp))

/-- If a command is `AuthorizedL` by `issuer`, its `cap` slot is necessarily
`some (issuer says _)`. -/
theorem authorizedL_cap_shape {c : Command} {issuer : Principal}
    (h : AuthorizedL c issuer) :
    ∃ capProp, c.cap = some (Prop'.says issuer capProp) := by
  obtain ⟨_, _, capProp, hcap, _⟩ := h
  exact ⟨capProp, hcap⟩

/-- **The right-reason bite.** A command with NO capability (`cap = none`) can
never be `AuthorizedL` — there is no `says`-guard to prove. -/
theorem not_authorizedL_of_cap_none {c : Command} {issuer : Principal}
    (h : c.cap = none) : ¬ AuthorizedL c issuer := by
  rintro ⟨_, _, _, hcap, _⟩
  rw [h] at hcap
  simp at hcap

/-- The authorizing principal is pinned by the command's guard. -/
theorem authorizedL_issuer_pinned {c : Command} {issuer p : Principal} {capProp : Prop'}
    (hshape : c.cap = some (Prop'.says issuer capProp)) (ha : AuthorizedL c p) :
    p = issuer := by
  obtain ⟨_, _, _, hcap, _⟩ := ha
  rw [hshape] at hcap
  injection hcap with hcap
  injection hcap with hp _
  exact hp.symm

/-! ## 3. Well-formed logs and the linear capability-safety metatheorem. -/

/-- **Provenance of a committed log (linear layer).** The empty log is
well-formed; committing an `AuthorizedL` command onto a well-formed log keeps it
well-formed. Every `commit` node carries its `AuthorizedL` proof — the sole way
the committed log grows. NOT "every element is authorized"; that is the theorem. -/
inductive WellFormedLogL : CommittedLog → Prop where
  /-- The empty log is trivially well-formed. -/
  | nil : WellFormedLogL []
  /-- Extending a well-formed log by an `AuthorizedL` command keeps it
  well-formed; the `AuthorizedL` proof is a field of the constructor. -/
  | commit {log : CommittedLog} {c : Command} {issuer : Principal}
      (h : WellFormedLogL log) (auth : AuthorizedL c issuer) :
      WellFormedLogL (log ++ [c])

/-- **THE METATHEOREM (linear layer).** Every command in a well-formed committed
log was authorized by a linear (`CDerivS`) signed credential. A genuine
induction over provenance — it EXTRACTS authorization from the chain of `commit`
nodes, mirroring `DLCD.capability_safety`. -/
theorem capability_safety_linear (log : CommittedLog) (hwf : WellFormedLogL log) :
    ∀ c ∈ log, ∃ issuer, AuthorizedL c issuer := by
  induction hwf with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil)
  | @commit log c' issuer h auth ih =>
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih c hc
      · rw [List.mem_singleton] at hc
        subst hc
        exact ⟨issuer, auth⟩

/-! ## 4. Anti-vacuity — a concrete AUTHORIZED write via a REAL linear credential.

A genuine linear signed credential `CDerivS.saysI issuer sig (.embed (CDeriv.var …))`
over the linear (`Mult.one`) context `[(writeCap, one)]`, a write guarded by it,
admitted to a `WellFormedLogL`, and capability-safety recovering its
authorization. Nothing here is opaque or vacuous. -/

namespace CapSafetyLinearAntiVacuity

/-- The issuing principal. -/
def issuer : Principal := Principal.atom ⟨[7]⟩

/-- The write capability (an atom stands in for the nucleus write-grant). -/
def writeCap : Prop' := Prop'.atom 5

/-- The Ed25519 signature carrier (opaque at the logical level; T2 says the
logical `saysI` and the cryptographic `⊢_K` coincide under EUF-CMA). -/
def sig : Signature := ⟨0, []⟩

/-- The value written by the command. -/
def value : Term := Term.var 0

/-- The **LINEAR** context: a single `Mult.one` (use-exactly-once) hypothesis
carrying the write capability. This is what makes the credential linear. -/
def Γ0 : Carve.Ctx Prop' := [(writeCap, Mult.one)]

/-- Position 0 of `Γ0` is the only used hypothesis; every other position is
`zero` (there are none), so `AllZeroExcept Γ0 0` holds. -/
theorem azx : AllZeroExcept Γ0 0 := by
  intro j p hj hlk
  cases j with
  | zero => exact absurd rfl hj
  | succ k =>
      simp only [Γ0, List.getElem?_cons_succ, List.getElem?_nil] at hlk
      exact absurd hlk (by simp)

/-- The **linear leaf**: a CARVe `var` derivation of `writeCap` under the linear
context `Γ0`. The used hypothesis is `Mult.one` (non-`zero`), and it is the only
live position (`azx`). -/
def leaf : CDeriv Γ0 (Term.var 0) writeCap :=
  CDeriv.var (i := 0) (φ := writeCap) (m := Mult.one)
    (by rfl) (by intro h; exact Mult.noConfusion h) azx

/-- **The real linear signed credential.** `CDerivS.saysI` seals the embedded
linear leaf into a signed affirmation `Term.sign issuer (var 0) sig :
issuer says writeCap`, over the SAME linear context `Γ0` (resources unchanged).
This is a genuine `CDerivS` says-credential, not an opaque assumption. -/
def saysWitnessL :
    CDerivS Γ0 (Term.sign issuer (Term.var 0) sig) (Prop'.says issuer writeCap) :=
  CDerivS.saysI issuer sig (CDerivS.embed leaf)

/-- The authorized write-command, guarded by `issuer says writeCap`. -/
def cmd : Command := writeCommand issuer writeCap value

/-- `cmd` is `AuthorizedL` by `issuer` — witnessed by the real linear signed
credential. This is the proof you must hold to admit the command. -/
theorem cmd_authorized : AuthorizedL cmd issuer :=
  ⟨Γ0, Term.sign issuer (Term.var 0) sig, writeCap, rfl, ⟨saysWitnessL⟩⟩

/-- The authorized write, admitted to a well-formed log. Type-checks ONLY
because `cmd_authorized` is supplied. -/
theorem admitted : WellFormedLogL ([] ++ [cmd]) :=
  WellFormedLogL.commit WellFormedLogL.nil cmd_authorized

/-- The write really is in the committed log. -/
theorem cmd_in_log : cmd ∈ ([] ++ [cmd]) := by simp

/-- **Non-vacuity of `capability_safety_linear`.** The metatheorem recovers an
authorization for the committed write — inhabited, not vacuous. -/
theorem recovered_authorized : ∃ issuer', AuthorizedL cmd issuer' :=
  capability_safety_linear ([] ++ [cmd]) admitted cmd cmd_in_log

/-! ### The bite — an UNAUTHORIZED command is rejected for the right reason. -/

/-- An unguarded command: no capability (`cap = none`). -/
def unauthCmd : Command := { payload := Term.var 0, cap := none }

/-- **The bite.** The unguarded command is genuinely NOT `AuthorizedL` — there
is no `says`-guard, so the credential requirement is unsatisfiable. The
`WellFormedLogL.commit` gate literally cannot be called for it. -/
theorem unauth_not_authorizedL : ¬ AuthorizedL unauthCmd issuer :=
  not_authorizedL_of_cap_none rfl

end CapSafetyLinearAntiVacuity

end DLCD
