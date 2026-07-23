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

/-! ## 6. Capability-safety by `commit-I` INVERSION (R1-inc4a).

Sections 1–5 recover authorization from an **out-of-band audit**: `Authorized`
asserts that a `says`-credential witness *exists* for the command's `cap` slot,
and `WellFormedLog` threads that audit through the commit provenance. R1-inc4a
re-founds the guarantee on the **type of the first-classed command term**: the
`commit-I`-typed `Term.command M c ℓ` (`DLC.Deriv.commitI`) is the *sole* `Deriv`
constructor whose subject is a `Term.command`, so a derivation of its type
**inverts** to the two `commit-I` premises — in particular the credential
derivation `dc : Deriv _ c (issuer says capProp)`. Authorization is then not an
audited side-condition; it is **extracted by inverting the typing of the command
itself** (a *generation lemma*, TAPL §13.5).

### Method (web-searched 2026-07-23; URLs recorded)
Type-safety is proved by *progress* (canonical-forms lemmas: a value at type `T`
has `T`'s introduction shape) and *preservation* (**inversion / generation**
lemmas: a derivation for a term of a given head shape can only have come from
that head's rule). Re-expressing "the committed write was authorized" as an
inversion on `commit-I` is exactly a generation lemma. The `Rsm.Command` wrapper
is the **abstract log-entry representation** the quorum/convergence machinery is
proven over; `Term.command`, related by `CommandRealizes` below, is its **typed
realization** — a data-refinement / representation-independence relation
(Reynolds), not a bijection (`rc.cap : Option Prop'` is a *proposition*; `c` is
its *proof term*; `ℓ` is a free parameter with no wrapper field).

- TAPL §13.5 *Safety* (progress via canonical forms; preservation via inversion):
  https://flylib.com/books/en/4.279.1.82/1/
- Harper, *PFPL* ch. 6 *Type Safety* (generation/inversion lemmas):
  https://www.khoury.northeastern.edu/~cmartens/Courses/7400-f24/pfpl/6-type-safety.pdf
- Grossman, *CS152 Lecture 10 — Type-Safety Proof* (progress+preservation split):
  https://homes.cs.washington.edu/~djg/2011sp/lec10_6up.pdf
- Twelf, *Canonical forms lemma*: http://twelf.org/wiki/Canonical_forms_lemma
- Reynolds, *Types, Abstraction and Parametric Polymorphism* (representation
  independence — the guarantee is stated over abstract behaviour, preserved under
  a representation change): https://people.mpi-sws.org/~dreyer/tor/papers/reynolds.pdf

`#print axioms` for every theorem below stays within `[propext]` (⊂ the permitted
`[propext, Classical.choice, Quot.sound]`). No `sorry`, no `native_decide`. The
governed `capability_safety` (§3) is **untouched, byte-identical** — this section
is purely additive. -/

/-- **The generation (inversion) lemma for `commit-I`, generalized-subject form.**
`Term.command _ _ _` is the subject of a *single* `Deriv` constructor whose
subject is literally a `command` (`commitI`). But a naive `cases d` does NOT
suffice: two rules have non-rigid subjects that can still *unify* with a command
head — `weakenA` (subject `shift M 1 0`, a function application) and `withinE`
(subject-preserving: subject `= M`, arbitrary). So the honest generation lemma is
proved by **induction on the derivation with a generalized subject** `t` plus the
equation `t = command M c ℓ`:

- the ~26 rigid-headed constructors are discharged by `Term.noConfusion` (their
  subject head ≠ `command`);
- `withinE` is discharged by the IH yielding a **type-shape contradiction**: a
  `command` typed via `withinE` would have `Prop'.within τ φ =
  Prop'.replicated (φ⊃φ) ℓ`, impossible;
- `weakenA` is handled genuinely: `shift M' 1 0 = command …` forces `M'` itself
  to be a `command` (by `shift`'s structural clause `shift (command m c l) = command …`),
  the IH recovers the credential and transformer for the unshifted subterms, and
  **re-applying `weakenA`** lifts them through the added additive hypothesis.

The **credential premise is recovered from the value's type** — capability-safety
re-founded: authorization is not an out-of-band audit, it is *extracted by
inverting the command's own typing*. `issuer`/`capProp` are **not pinned by the
conclusion** (`Replicated (φ⊃φ) ℓ` omits them); they live only in the credential
premise, recovered existentially. -/
theorem command_typing_inversion_aux
    {Γ : Ctx} {t : Term} {ψ : Prop'} (d : Deriv Γ t ψ) :
    ∀ (M c : Term) (ℓ : Label), t = Term.command M c ℓ →
    ∃ (Γₐ : List Prop') (issuer : Principal) (capProp φ : Prop'),
      Γ = { additive := Γₐ, linear := [] } ∧
      ψ = Prop'.replicated (Prop'.imp φ φ) ℓ ∧
      Nonempty (Deriv { additive := Γₐ, linear := [] } c (Prop'.says issuer capProp)) ∧
      Nonempty (Deriv { additive := Γₐ, linear := [] } M (Prop'.imp φ φ)) := by
  induction d
  case commitI Γₐ issuer capProp φ ℓ' M' c' dc dM dc_ih dM_ih =>
      intro M c ℓ heq
      injection heq with hM hc hℓ
      subst hM; subst hc; subst hℓ
      exact ⟨Γₐ, issuer, capProp, φ, rfl, rfl, ⟨dc⟩, ⟨dM⟩⟩
  case weakenA Γ' φ' φw M' d' ih =>
      intro M c ℓ heq
      cases M'
      case command m₀ c₀ ℓ₀ =>
          simp only [shift] at heq
          injection heq with hM hc hℓ
          subst hM; subst hc; subst hℓ
          obtain ⟨Γ'ₐ, issuer, capProp, φ₀, hΓ', hψ', hcred, htrans⟩ := ih m₀ c₀ ℓ₀ rfl
          subst hΓ'
          obtain ⟨dcred⟩ := hcred
          obtain ⟨dtrans⟩ := htrans
          exact ⟨φ' :: Γ'ₐ, issuer, capProp, φ₀, rfl, hψ',
                 ⟨Deriv.weakenA _ φ' _ _ dcred⟩, ⟨Deriv.weakenA _ φ' _ _ dtrans⟩⟩
      all_goals (simp only [shift] at heq; exact Term.noConfusion heq)
  case withinE Γ' τ φw M' d' ih =>
      intro M c ℓ heq
      obtain ⟨_, _, _, _, _, hψ, _, _⟩ := ih M c ℓ heq
      exact absurd hψ (by simp)
  all_goals (intro M c ℓ heq; exact Term.noConfusion heq)

/-- **The generation (inversion) lemma for `commit-I`.** From a derivation of a
`Term.command M c ℓ`'s type, recover the two `commit-I` premises — in particular
the credential derivation `dc : Deriv _ c (issuer says capProp)`. Direct
corollary of `command_typing_inversion_aux` at `t := Term.command M c ℓ`. -/
theorem command_typing_inversion
    {Γ : Ctx} {M c : Term} {ℓ : Label} {ψ : Prop'}
    (d : Deriv Γ (Term.command M c ℓ) ψ) :
    ∃ (Γₐ : List Prop') (issuer : Principal) (capProp φ : Prop'),
      Γ = { additive := Γₐ, linear := [] } ∧
      ψ = Prop'.replicated (Prop'.imp φ φ) ℓ ∧
      Nonempty (Deriv { additive := Γₐ, linear := [] } c (Prop'.says issuer capProp)) ∧
      Nonempty (Deriv { additive := Γₐ, linear := [] } M (Prop'.imp φ φ)) :=
  command_typing_inversion_aux d M c ℓ rfl

/-- **Capability-safety, typing-native form.** From the *type* of a
`commit-I`-typed command, recover a genuine `says`-credential derivation for its
credential subterm `c`. This is capability-safety recovered from the TYPE — not
from an audited `WellFormedLog` side-condition. `issuer` is existential
(matching the `∃ issuer` shape of the governed `capability_safety`), because
`commit-I`'s conclusion omits it. -/
theorem capability_safety_by_inversion
    {Γ : Ctx} {M c : Term} {ℓ : Label} {φ : Prop'}
    (d : Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ)) :
    ∃ (issuer : Principal) (capProp : Prop') (Δ : Ctx),
      Nonempty (Deriv Δ c (Prop'.says issuer capProp)) := by
  obtain ⟨Γₐ, issuer, capProp, _φ', _, _, hc, _⟩ := command_typing_inversion d
  exact ⟨issuer, capProp, _, hc⟩

/-! ### The realization relation — `Rsm.Command` ⟵ `Term.command`.

`CommandRealizes rc M c ℓ Γ issuer capProp φ` is the abstraction/refinement
relation between the **abstract log-entry** `rc : Command` and its **typed
realization** `Term.command M c ℓ`. It is NOT a bijection: the wrapper's
`cap : Option Prop'` is a *proposition*; the term's `c` is a *proof term* of it;
and `ℓ` is a free parameter the wrapper has no field for (RULING: `ℓ` is a
parameter of the relation, not a new `Command` field). The third conjunct is the
load-bearing **coherence** condition — the wrapper's `cap` slot is *exactly the
proposition the credential subterm `c` proves*; it is NOT derivable from the
fourth conjunct alone, since `commit-I`'s conclusion hides the credential's
proposition (`command_typing_inversion` recovers a *free* `issuer'/capProp'`). -/
def CommandRealizes
    (rc : Command) (M c : Term) (ℓ : Label)
    (Γ : Ctx) (issuer : Principal) (capProp φ : Prop') : Prop :=
  rc.payload = M ∧
  rc.cap = some (Prop'.says issuer capProp) ∧
  Nonempty (Deriv Γ c (Prop'.says issuer capProp)) ∧
  Nonempty (Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ))

/-! ### The coincidence bridge — audited `Authorized` ⟷ `commit-I`-typeability.

Two directions close cleanly; one direction is honestly fenced. -/

/-- **Bridge (→), clean.** A `commit-I`-typeable `Term.command M c ℓ` *is* an
authorized wrapper: the credential subterm `c` is the very witness the audited
`Authorized` demands, and the wrapper whose `cap` slot carries the recovered
credential proposition `issuer says capProp` is `Authorized` by that same
`issuer`. So the audited side-condition is **backed by the typing**: it is not a
free-standing audit but a shadow of `commit-I`-typeability. (`issuer`/`capProp`
are existential because the command's conclusion omits them; the credential TERM
`c` is the concrete `Authorized`-witness.) -/
theorem authorized_of_command_typing
    {Γ : Ctx} {M c : Term} {ℓ : Label} {φ : Prop'}
    (d : Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ)) :
    ∃ (issuer : Principal) (capProp : Prop'),
      Authorized (⟨M, some (Prop'.says issuer capProp)⟩ : Command) issuer := by
  obtain ⟨Γₐ, issuer, capProp, _φ', _, _, hc, _⟩ := command_typing_inversion d
  exact ⟨issuer, capProp, { additive := Γₐ, linear := [] }, c, capProp, rfl, hc⟩

/-- **Bridge (→) via the relation, clean.** Whenever `rc` is realized by a
commit-I-typeable command, `rc` is `Authorized` by the realization's `issuer` —
the coherence conjunct of `CommandRealizes` supplies exactly the credential the
audit needs. This shows the abstract-rep audit `Authorized` is *implied by* the
typed-realization relation. -/
theorem authorized_of_commandRealizes
    {rc : Command} {M c : Term} {ℓ : Label} {Γ : Ctx}
    {issuer : Principal} {capProp φ : Prop'}
    (h : CommandRealizes rc M c ℓ Γ issuer capProp φ) :
    Authorized rc issuer := by
  obtain ⟨_hpay, hcap, hc, _⟩ := h
  exact ⟨Γ, c, capProp, hcap, hc⟩

/-- **Bridge (←) at the premise level, clean (the realization BUILDER).** Given
the two `commit-I` premises — a credential `c : issuer says capProp` and a store
transformer `M : φ ⊃ φ`, both in a shared linear-free context — the wrapper
`⟨M, some (issuer says capProp)⟩` is realized by the commit-I-typeable
`Term.command M c ℓ` (for any supplied `ℓ`). This is the constructive converse
of `command_typing_inversion`, and witnesses that `CommandRealizes` is
satisfiable (anti-vacuity for the relation).

**FENCE — the FULL converse `Authorized rc issuer → ∃ …, CommandRealizes …` does
NOT close cleanly**, for two independent reasons the audit cannot supply:
(1) `Authorized`'s credential derivation lives in an *arbitrary* `Γ : Ctx` (its
linear context may be non-empty), whereas `commit-I` demands a *linear-free*
shared context `{ additive := Γₐ, linear := [] }`; and (2) `Authorized` carries
no store transformer `M : φ ⊃ φ` — `commit-I`'s second premise — and none can be
synthesized from the credential alone. This is the credential-prop ↔ credential-
term / representation gap (`cap` is a proposition, `command` additionally needs a
typed transformer and a label). The builder below closes the converse exactly
when those two data are supplied. -/
theorem commandRealizes_of_premises
    {Γₐ : List Prop'} {M c : Term} {ℓ : Label}
    {issuer : Principal} {capProp φ : Prop'}
    (dc : Deriv { additive := Γₐ, linear := [] } c (Prop'.says issuer capProp))
    (dM : Deriv { additive := Γₐ, linear := [] } M (Prop'.imp φ φ)) :
    CommandRealizes (⟨M, some (Prop'.says issuer capProp)⟩ : Command)
      M c ℓ { additive := Γₐ, linear := [] } issuer capProp φ :=
  ⟨rfl, rfl, ⟨dc⟩, ⟨Deriv.commitI Γₐ issuer capProp φ ℓ M c dc dM⟩⟩

/-! ## 7. Anti-vacuity — a concrete `commit-I`-typed command, credential recovered.

A REAL signed credential (`CapSafetyAntiVacuity.saysWitness` = `Deriv.saysI`),
paired with an identity store transformer, committed as a `commit-I`-typed
`Term.command`, and `capability_safety_by_inversion` recovering a genuine
`says`-credential from its TYPE. Nothing here is vacuous. -/

namespace CapSafetyByInversionAntiVacuity

open CapSafetyAntiVacuity (issuer writeCap sig saysWitness)

/-- The identity store transformer `λ (x : writeCap). x`, a `commit-I`
second premise `M : writeCap ⊃ writeCap` in the credential's context. -/
def transformer : Term := Term.lam writeCap (Term.var 0)

/-- `transformer : writeCap ⊃ writeCap`, in the same linear-free context
`{ additive := [writeCap], linear := [] }` as `saysWitness`. -/
def transformerDeriv :
    Deriv { additive := [writeCap], linear := [] }
      transformer (Prop'.imp writeCap writeCap) :=
  Deriv.impI { additive := [writeCap], linear := [] } writeCap writeCap
    (Term.var 0) (Deriv.varA _ 0 writeCap rfl)

/-- The first-classed capability-gated write, as a `Term.command`: the identity
transformer, guarded by the real signed credential `sign issuer (var 0) sig`,
at label `Label.bottom`. -/
def commandTerm : Term :=
  Term.command transformer (Term.sign issuer (Term.var 0) sig) Label.bottom

/-- **The `commit-I` derivation.** `commandTerm` types at
`Replicated (writeCap ⊃ writeCap) ⊥` — the credential premise is the genuine
`saysWitness`, the transformer premise is `transformerDeriv`. This is the
proof-carrying command whose TYPE alone certifies authorization. -/
def commandDeriv :
    Deriv { additive := [writeCap], linear := [] }
      commandTerm (Prop'.replicated (Prop'.imp writeCap writeCap) Label.bottom) :=
  Deriv.commitI [writeCap] issuer writeCap writeCap Label.bottom
    transformer (Term.sign issuer (Term.var 0) sig) saysWitness transformerDeriv

/-- **Non-vacuity of `capability_safety_by_inversion`.** Inverting the TYPE of
the concrete `commit-I`-typed command recovers a REAL `says`-credential
derivation for its credential subterm — inhabited, not vacuous. -/
theorem recovered_credential_by_inversion :
    ∃ (issuer' : Principal) (capProp : Prop') (Δ : Ctx),
      Nonempty (Deriv Δ (Term.sign issuer (Term.var 0) sig)
        (Prop'.says issuer' capProp)) :=
  capability_safety_by_inversion commandDeriv

/-- **Non-vacuity of the coincidence bridge.** The concrete command's TYPE yields
an `Authorized` wrapper — the audited side-condition, recovered from the type. -/
theorem recovered_authorized_by_typing :
    ∃ (issuer' : Principal) (capProp : Prop'),
      Authorized (⟨transformer, some (Prop'.says issuer' capProp)⟩ : Command) issuer' :=
  authorized_of_command_typing commandDeriv

/-- **Non-vacuity of the realization relation.** The two commit-I premises build
a satisfying instance of `CommandRealizes` — the relation is inhabited. -/
theorem commandRealizes_witness :
    CommandRealizes (⟨transformer, some (Prop'.says issuer writeCap)⟩ : Command)
      transformer (Term.sign issuer (Term.var 0) sig) Label.bottom
      { additive := [writeCap], linear := [] } issuer writeCap writeCap :=
  commandRealizes_of_premises saysWitness transformerDeriv

/-- …and that realization implies the audited `Authorized` (bridge →, on the
concrete witness). -/
theorem realized_is_authorized :
    Authorized (⟨transformer, some (Prop'.says issuer writeCap)⟩ : Command) issuer :=
  authorized_of_commandRealizes commandRealizes_witness

end CapSafetyByInversionAntiVacuity

end DLCD
