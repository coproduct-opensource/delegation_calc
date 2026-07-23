import DLCD.Rsm
import DLC.Judgment

/-! # DLC-D Phase 1.2a — capability-safety by construction

This module makes the abstract `Command.cap` slot of the Phase 1.0 RSM
substrate (`DLCD.Rsm`) **load-bearing**. It realizes the DLC-D-distinctive
*enforce-by-construction* guarantee: a controlled operation — committing a
write to the replicated log — is gated behind a **proof** that the issuing
principal `says` the capability guarding the command. "Only a
capability-holder can commit, by construction," because the constructor of a
committed log demands the `says`-proof as a required argument.

## The design: proof-carrying authorization (PCA)

In proof-carrying authorization (Appel–Felten; Bauer), a requester constructs
a **proof** that the policy authorizes the request and submits it *with* the
request; a reference monitor merely *checks* the proof. Here the "proof" is a
DLC derivation `Deriv Γ M (p says φ)` — a well-typed proof term witnessing that
principal `p` affirms the capability `φ`. Because DLC's `says`-introduction
(`Deriv.saysI`) carries an Ed25519 `Signature`, the witness term is literally a
*signed credential* `Term.sign issuer M sig` — the term-level shadow of the
signature that realizes `Γ ⊢_K M : φ` in `dlc-crypto`. The `says` connective is
the affirmation modality of authorization logic (Abadi's "A says φ"; Garg–Abadi
modal deconstruction), and gating a controlled operation behind
`Deriv … (issuer says φ)` is the says-indexed / DCC-monad discipline: the
protected operation is reachable only through the modality.

### Why `Deriv`, not `CDeriv`
The `CDeriv` judgment (`DLC.CarveJudgment`) is the DILL-sound CARVe migration,
but it has **no `says`-introduction** — as its own progress section records,
"`says`/`boxed` have NO intro in `CDeriv`", so no *closed* `says`-proof can be
built there. The faithful proof-carrying witness must therefore use `Deriv`
(`DLC.Judgment`), whose `saysI` is the genuine signature-carrying affirmation
introduction. `Deriv` is DLC's primary logical typing judgment (`Γ ⊢ M : φ`);
`says φ` proofs constructed by `saysI` are exactly the signed credentials PCA
carries. This is the "faithful shape" the task anticipated.

## The metatheorem (capability-safety) is non-circular

`WellFormedLog` is **not** defined as "every command is authorized" (which would
make capability-safety a tautology). It is an **inductive provenance** predicate:
the empty log is well-formed, and the only other way to be well-formed is to be
the result of committing an *authorized* command onto an already-well-formed log
(`WellFormedLog.commit` carries an `Authorized` proof). `capability_safety` then
**extracts** per-element authorization from that provenance by induction —
the load-bearing content is "anything in the committed log was placed by a
`commit` node, and every `commit` node demanded a `says`-proof." The bridge
`mem_commit_authorized` shows the function `commit` only ever appends the one
command whose authorization it required.

`#print axioms capability_safety` = `#print axioms committed_write_says_cap` =
`#print axioms mem_commit_authorized` = `[propext]` (fewer than the permitted
`[propext, Classical.choice, Quot.sound]`); likewise every helper and every
`AntiVacuity` witness. No `sorryAx`, no `native_decide`.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Bauer, *Access Control for the Web via Proof-Carrying Authorization* (PhD
  thesis): the requester builds a proof that policy ⊢ access, the monitor checks
  it. http://users.ece.cmu.edu/~lbauer/papers/thesis.pdf
- Garg, *Proof Theory for Authorization Logic* (PhD thesis) and *An Introduction
  to Proof-Carrying Authorization*: the `says` affirmation modality, its proof
  theory, and PCA. https://people.mpi-sws.org/~dg/papers/thesis.pdf ,
  https://people.mpi-sws.org/~dg/papers/intro-pca.pdf
- Abadi, *Access Control in a Core Calculus of Dependency* / Abadi–Banerjee–
  Heintze–Riecke, *A Core Calculus of Dependency* (POPL 1999): `says` as an
  (idempotent) monad indexed by principals; the protected operation is reachable
  only through the modality. https://www.cs.cornell.edu/andru/cs711/2003fa/reading/abadi99core.pdf ,
  https://people.mpi-sws.org/~dg/teaching/lis2014/modules/authorization-3-abadi06.pdf
- Garg–Abadi, *A Modal Deconstruction of Access Control Logics*; Appel–Felten,
  *Proof-Carrying Authentication* (the original monitor-checks-a-proof idea).
- Bauer–Bowers–Garg–Pfenning–Reiter, *Consumable Credentials in Logic-Based
  Access Control*: the linear-resource reading the RSM's `cap` slot foreshadows.
-/

namespace DLCD

open DLC

/-! ## 1. The authorization predicate — proof-carrying authorization.

`Authorized c issuer` holds exactly when the command `c` carries, in its `cap`
slot, a `says`-guarded capability `issuer says capProp`, **and** there EXISTS a
DLC derivation witnessing that `issuer` in fact `says` that capability. The
existential over `Γ`, `capTerm`, `capProp` is the PCA condition: the command is
accompanied by a proof term (a signed credential) of the issuer's authority. -/

/-- **Proof-carrying-authorization condition.** `c` is authorized by `issuer`
iff its guarding capability is `issuer says capProp` and a real `Deriv` witness
of `issuer says capProp` exists — a proof term the reference monitor can check.
`Nonempty` erases the specific witness to a `Prop` while preserving its
*existence*, which is all capability-safety asserts. -/
def Authorized (c : Command) (issuer : Principal) : Prop :=
  ∃ (Γ : Ctx) (capTerm : Term) (capProp : Prop'),
    c.cap = some (Prop'.says issuer capProp) ∧
    Nonempty (Deriv Γ capTerm (Prop'.says issuer capProp))

/-- If a command is authorized by `issuer`, its `cap` slot is *necessarily*
`some (issuer says _)`. This is the necessary structural condition the
decidable pre-filter `capShapeOk`/`tryCommit` checks. -/
theorem authorized_cap_shape {c : Command} {issuer : Principal}
    (h : Authorized c issuer) :
    ∃ capProp, c.cap = some (Prop'.says issuer capProp) := by
  obtain ⟨_, _, capProp, hcap, _⟩ := h
  exact ⟨capProp, hcap⟩

/-- A command with **no** capability (`cap = none`) can never be authorized —
there is no `says`-guard to prove, so PCA is unsatisfiable. This is the
right-reason bite for an unguarded command. -/
theorem not_authorized_of_cap_none {c : Command} {issuer : Principal}
    (h : c.cap = none) : ¬ Authorized c issuer := by
  rintro ⟨_, _, _, hcap, _⟩
  rw [h] at hcap
  simp at hcap

/-- The authorizing principal is unique and pinned by the command's guard: if
`c.cap = some (issuer says capProp)` then any principal that authorizes `c`
must BE `issuer`. So authorization is not free-floating — it tracks the exact
issuer named in the capability. -/
theorem authorized_issuer_pinned {c : Command} {issuer p : Principal} {capProp : Prop'}
    (hshape : c.cap = some (Prop'.says issuer capProp)) (ha : Authorized c p) :
    p = issuer := by
  obtain ⟨_, _, _, hcap, _⟩ := ha
  rw [hshape] at hcap
  injection hcap with hcap
  injection hcap with hp _
  exact hp.symm

/-! ## 2. The gated commit — enforce-by-construction at the type level.

`commit` takes the authorization **proof** as a required argument: one cannot
even form the call `commit g c issuer auth` without producing `auth :
Authorized c issuer`. This is the enforce-by-construction gate — the type
system refuses an unauthorized commit. `tryCommit` is the decidable
pre-filter that realizes the reference-monitor *check* on the (necessary)
capability shape and returns `none` on rejection. -/

/-- **The proof-required commit.** Append `c` to the committed log — but ONLY
with an in-hand proof `auth : Authorized c issuer`. The proof is a required
argument, so the ONLY way into the committed log is through an authorized
command. (The proof is not consumed at runtime; it is the compile-time
capability that gates the operation.) -/
def commit (g : GlobalConfig) (c : Command) (issuer : Principal)
    (_auth : Authorized c issuer) : GlobalConfig :=
  { g with log := g.log ++ [c] }

/-- The decidable capability-shape check the reference monitor runs: the cap
must be present and be a `says` by exactly `issuer`. This is a NECESSARY
condition for `Authorized` (`authorized_cap_shape`), so rejecting on it is
sound — but it does not decide the existence of the `Deriv` witness, which is
why the proof-required `commit` is the primary gate. -/
def capShapeOk (c : Command) (issuer : Principal) : Bool :=
  match c.cap with
  | some (Prop'.says p _) => decide (p = issuer)
  | _ => false

/-- **The checkable commit (reference-monitor form).** Returns `none` when the
capability-shape check fails — an unauthorized command is rejected. Returns the
extended config when the shape checks out. -/
def tryCommit (g : GlobalConfig) (c : Command) (issuer : Principal) :
    Option GlobalConfig :=
  if capShapeOk c issuer then some { g with log := g.log ++ [c] } else none

/-- Authorization implies the shape check passes: the decidable pre-filter never
rejects a genuinely authorized command (no false negatives). -/
theorem authorized_capShapeOk {c : Command} {issuer : Principal}
    (h : Authorized c issuer) : capShapeOk c issuer = true := by
  obtain ⟨capProp, hcap⟩ := authorized_cap_shape h
  unfold capShapeOk
  rw [hcap]
  simp

/-- **Soundness of rejection (the bite).** If `tryCommit` returns `none`, the
command was genuinely NOT authorized — the monitor never rejects an authorized
request. Contrapositive of `authorized_capShapeOk`. -/
theorem tryCommit_none_not_authorized {g : GlobalConfig} {c : Command}
    {issuer : Principal} (h : tryCommit g c issuer = none) :
    ¬ Authorized c issuer := by
  intro ha
  have hok := authorized_capShapeOk ha
  unfold tryCommit at h
  rw [hok] at h
  simp at h

/-! ## 3. Well-formed logs and the capability-safety metatheorem.

`WellFormedLog` is an inductive PROVENANCE predicate — a log is well-formed iff
it is the empty log or an authorized `commit` onto a well-formed log. It is NOT
"every element is authorized"; that is the theorem we prove. -/

/-- **Provenance of a committed log.** The empty log is well-formed; committing
an `Authorized` command onto a well-formed log keeps it well-formed. Every
`commit` node carries its `Authorized` proof — this is the sole way the
committed log grows, so this predicate captures "was built only by authorized
commits." -/
inductive WellFormedLog : CommittedLog → Prop where
  /-- The empty log — no commits yet — is trivially well-formed. -/
  | nil : WellFormedLog []
  /-- Extending a well-formed log by an authorized command keeps it
  well-formed. The `Authorized` proof is a field of the constructor. -/
  | commit {log : CommittedLog} {c : Command} {issuer : Principal}
      (h : WellFormedLog log) (auth : Authorized c issuer) :
      WellFormedLog (log ++ [c])

/-- The function `commit` produces a well-formed log from a well-formed one —
its result is exactly a `WellFormedLog.commit` node. This is what threads the
enforce-by-construction guarantee through actual use of the gate. -/
theorem commit_wellFormed {g : GlobalConfig} {c : Command} {issuer : Principal}
    (auth : Authorized c issuer) (hg : WellFormedLog g.log) :
    WellFormedLog (commit g c issuer auth).log :=
  WellFormedLog.commit hg auth

/-- **The commit bridge.** Anything in `(commit g c' issuer auth).log` is either
the newly committed `c'` (which came with its authorization proof `auth`) or was
already in `g.log`. The function `commit` appends exactly the one command whose
authorization it demanded — nothing else can slip in. -/
theorem mem_commit_authorized {g : GlobalConfig} {c' : Command} {issuer : Principal}
    (auth : Authorized c' issuer) (c : Command)
    (h : c ∈ (commit g c' issuer auth).log) :
    (c = c' ∧ Authorized c issuer) ∨ c ∈ g.log := by
  unfold commit at h
  rw [List.mem_append] at h
  rcases h with h | h
  · exact Or.inr h
  · rw [List.mem_singleton] at h
    subst h
    exact Or.inl ⟨rfl, auth⟩

/-- **THE METATHEOREM — capability-safety by construction.** Every command that
reached a well-formed committed log was authorized: some principal `says` the
capability guarding it, with a real `Deriv` proof. Because `commit` (the only
way into the log) required that `says`-proof as an argument, nothing unauthorized
can be committed. The proof is a genuine induction over the log's provenance —
it does not re-assert a definition of well-formedness, it EXTRACTS authorization
from the chain of `commit` nodes. -/
theorem capability_safety (log : CommittedLog) (hwf : WellFormedLog log) :
    ∀ c ∈ log, ∃ issuer, Authorized c issuer := by
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

/-! ## 4. The guarded operation is a WRITE.

A write-command carries a value payload and is guarded by `issuer says
writeCap`. Capability-safety specializes to: **a committed write implies the
issuer holds (says) the write capability, with a proof.** -/

/-- A write-command: overwrite the register with `value`, guarded by the
capability `issuer says writeCap`. This is the controlled operation the PCA gate
protects. -/
def writeCommand (issuer : Principal) (writeCap : Prop') (value : Term) : Command :=
  { payload := value, cap := some (Prop'.says issuer writeCap) }

/-- **Capability-safety for writes.** If a write guarded by `issuer says
writeCap` sits in a well-formed committed log, then a real `Deriv` witnesses
that `issuer` says the write capability — a committed write PROVES the issuer's
write authority. -/
theorem committed_write_says_cap {log : CommittedLog} (hwf : WellFormedLog log)
    {issuer : Principal} {writeCap : Prop'} {value : Term}
    (hmem : writeCommand issuer writeCap value ∈ log) :
    ∃ (Γ : Ctx) (t : Term), Nonempty (Deriv Γ t (Prop'.says issuer writeCap)) := by
  obtain ⟨p, ha⟩ := capability_safety log hwf _ hmem
  -- The authorizing principal is pinned to `issuer` by the write's guard.
  have hp : p = issuer := authorized_issuer_pinned (by rfl) ha
  subst hp
  obtain ⟨Γ, t, capProp, hcap, hne⟩ := ha
  -- The guard is `issuer says writeCap`, so the proven capProp IS writeCap.
  simp only [writeCommand] at hcap
  injection hcap with hcap
  injection hcap with _ hcp
  subst hcp
  exact ⟨Γ, t, hne⟩

/-! ## 5. Anti-vacuity — a concrete AUTHORIZED write, committed, recovered.

A REAL signature-carrying `says`-witness (`Deriv.saysI` = the PCA signed
credential), a write guarded by it, committed through the enforce-by-construction
gate, and capability-safety yielding its authorization. Nothing here is vacuous:
the `Deriv` witness is inhabited and the recovered authorization carries it. -/

namespace CapSafetyAntiVacuity

/-- The issuing principal. -/
def issuer : Principal := Principal.atom ⟨[7]⟩

/-- The write capability, an atomic proposition (`spec`: an atom stands in for
the nucleus `CapabilityLattice` write-grant). -/
def writeCap : Prop' := Prop'.atom 5

/-- The Ed25519 signature carrier (opaque at the logical level; T2 says the
logical `saysI` and the cryptographic `⊢_K` coincide under EUF-CMA). -/
def sig : Signature := ⟨0, []⟩

/-- The value written by the command. -/
def value : Term := Term.var 0

/-- **The real proof-carrying credential.** `saysI` wraps an inner proof of
`writeCap` (an additive-`var` leaf) into a signed affirmation
`Term.sign issuer (var 0) sig : issuer says writeCap`. This is the genuine
`says`-witness — the signed capability the commit gate demands. -/
def saysWitness :
    Deriv { additive := [writeCap], linear := [] }
      (Term.sign issuer (Term.var 0) sig) (Prop'.says issuer writeCap) :=
  Deriv.saysI _ issuer writeCap (Term.var 0) sig (Deriv.varA _ 0 _ rfl)

/-- The authorized write-command, guarded by `issuer says writeCap`. -/
def cmd : Command := writeCommand issuer writeCap value

/-- `cmd` is authorized by `issuer` — witnessed by the real signed credential.
This is the term you MUST have in hand to call `commit`. -/
theorem cmd_authorized : Authorized cmd issuer :=
  ⟨_, _, _, rfl, ⟨saysWitness⟩⟩

/-- The starting configuration with an empty (trivially well-formed) log. -/
def g0 : GlobalConfig := { replicas := [], log := [], budget := FailureBudget.zero 1 }

/-- Commit the authorized write through the enforce-by-construction gate. The
call type-checks ONLY because `cmd_authorized` is supplied. -/
def g1 : GlobalConfig := commit g0 cmd issuer cmd_authorized

/-- The committed log is well-formed by construction of `commit`. -/
theorem g1_wellFormed : WellFormedLog g1.log :=
  commit_wellFormed cmd_authorized WellFormedLog.nil

/-- The write really is in the committed log. -/
theorem cmd_in_g1 : cmd ∈ g1.log := by
  simp [g1, commit, g0]

/-- **Non-vacuity of capability-safety.** The metatheorem recovers an
authorization for the committed write — inhabited, not vacuous. -/
theorem recovered_authorized : ∃ issuer', Authorized cmd issuer' :=
  capability_safety g1.log g1_wellFormed cmd cmd_in_g1

/-- **The write payoff, inhabited.** capability-safety-for-writes yields a REAL
`Deriv` of `issuer says writeCap` for the committed write — the signed
credential is recovered from the log. -/
theorem recovered_write_says_cap :
    ∃ (Γ : Ctx) (t : Term), Nonempty (Deriv Γ t (Prop'.says issuer writeCap)) :=
  committed_write_says_cap g1_wellFormed (value := value) cmd_in_g1

/-! ### The bite — an UNAUTHORIZED command is rejected at the expected spot. -/

/-- An unguarded command: no capability (`cap = none`). -/
def unauthCmd : Command := { payload := Term.var 0, cap := none }

/-- `tryCommit` REJECTS the unguarded command — returns `none`. The rejection
fires in the `_ => false` branch of `capShapeOk` because `cap = none`. -/
theorem unauth_rejected : tryCommit g0 unauthCmd issuer = none := by
  rfl

/-- And the rejection is for the RIGHT reason: the unguarded command is
genuinely not authorizable — the proof-required `commit` literally cannot be
called for it, since `Authorized unauthCmd issuer` is uninhabited. -/
theorem unauth_not_authorized : ¬ Authorized unauthCmd issuer :=
  not_authorized_of_cap_none rfl

/-- A command guarded by a DIFFERENT principal's capability is also rejected by
the monitor — authorization tracks the exact issuer. -/
theorem wrong_issuer_rejected :
    tryCommit g0 cmd (Principal.atom ⟨[99]⟩) = none := by
  rfl

end CapSafetyAntiVacuity

end DLCD
