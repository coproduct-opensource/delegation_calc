# R2-inc3b — Reducer/model gap on `SaysBind` and `Discharge`: findings memo

**Status:** investigation for the author to rule on. Neutral. Brandon decides;
this memo informs.
**Investigated at:** worktree branch `dlc-d/phase0-carve`, HEAD `690bb39`
(the task named `3de65e3`; the worktree is a few commits ahead — the finding is
unchanged). Toolchain Lean `v4.30.0-rc2`, Rust workspace `dlc-*` v1.5.0.
**Author of the diverging commits:** all Brandon (see §5).

---

## 0. The finding, restated precisely

The R2.3b correspondence proof found that the deployed reducer
`crates/dlc-core/src/reduce.rs::step` and the hand-verified model
`lean/DLC/Reduce.lean::step` disagree on two head redexes:

| Constructor | `lean/DLC/Reduce.lean` | `crates/dlc-core/src/reduce.rs` |
|---|---|---|
| `LetSays`  | reduces (says-extract-β), :97–103 | **reduces**, :87–99 |
| `SaysBind` | reduces (says-extract-β), :90–96 | **frozen** — no arm; falls to `_ => None` |
| `Discharge`| reduces (discharge-β), :143–149  | **frozen** — no arm; falls to `_ => None` |
| `Declassify`| frozen, :154 | frozen, :129 |

Both codebases carry `SaysBind` **and** `LetSays` as distinct constructors
(`lean/DLC/Syntax.lean:87–88`, `crates/dlc-core/src/syntax.rs:72,125`). The gap
is specifically that the Rust runtime freezes `SaysBind` and `Discharge` while
the model reduces both. `LetSays` and `Declassify` agree across the two and are
not in dispute.

The question: **(a) FIX RUST** — add says-extract-β(`SaysBind`) and discharge-β
to `reduce.rs`, regenerate Aeneas, make the runtime match the model and spec; vs
**(b) FIX MODEL** — delete those two β-rules from `DLC.step`, make the model
match the current runtime.

---

## 1. Why `saysBind` AND `letSays` both exist, and whether `saysBind` should reduce

**They are two different typing rules with the same operational behavior.**

- `saysBind` is the spec's canonical **says-E** (`spec/typing-rules.md` §4,
  rule at line 90; `spec/syntax.md` grammar `saysBind_p(M,N)`). Its typing
  conclusion **preserves the modality**: from `M : p says φ` and a body typed
  under the extracted `x:φ`, it concludes `p says ψ`
  (`lean/DLC/Judgment.lean:125–136`, `Deriv.saysE` → `Term.saysBind`). The
  Syntax doc comment is explicit: "The conclusion PRESERVES the modality
  (`p says ψ`), which is what separates it from `letSays`"
  (`lean/DLC/Syntax.lean:79–86`).
- `letSays` is an **extra** rule (`Deriv.letSaysE`, `lean/DLC/Judgment.lean:310+`)
  whose conclusion **strips the modality** (`ψ`, no `says`). Commit `bcdfa27`
  flags it as an anomaly: "`letSaysE` … its conclusion STRIPS the modality …
  and it appears nowhere in the spec's rule index. Whether it should be specced
  or removed is open."

Operationally the two are **identical**: both eliminate a `p says φ` value by
extracting the signed payload — `let ⟨x⟩_p = ⟨m,σ⟩_p in body ▷ body[m/x]` when
the principals agree. The two `step` arms in `lean/DLC/Reduce.lean` (90–96 vs
97–103) are byte-for-byte the same modulo the constructor name. So **on the
model's own terms, `saysBind` must have the same says-extract reduction as
`letSays`.** There is no reading in which `saysBind` is a value or is eliminated
elsewhere: `Deriv.saysE` types it as an elimination form, and the payload it
binds has to be substituted for the reduct to make sense.

**Sub-conclusion:** the semantics say `saysBind` should reduce exactly as
`letSays` does. That the Rust runtime reduces `letSays` (the anomalous,
un-specced rule) but freezes `saysBind` (the spec's canonical says-E) is
backwards relative to the spec's own primacy. This points to **(a)**.

---

## 2. Is says-extract-β(`saysBind`) load-bearing? (experiment 2)

**Assessment method.** A full `lake build` of the affected libs requires
building Mathlib + Aeneas from source (no `.lake` cache present in the worktree;
Mathlib pinned at `v4.30.0-rc2`), which is a multi-hour cold build. The
load-bearing question was therefore answered by reading the exact proof
obligations that consume the `saysBind` arm of `step`, which pin the behavior
far more precisely than a green/red build would. Where a build would have
mattered — a witness that pins `step (saysBind …) = …` — I searched for one and
found none (`grep` for any `step` assertion on `saysBind` across `lean/` is
empty).

**Finding: says-extract-β(`saysBind`) is NOT load-bearing for any theorem
STATEMENT.**

- **Progress** (`lean/DLC/Progress.lean`) is proved over the decidable fragment
  `PropDeriv`, and `PropDeriv`/`decideLean` is **fail-closed on says-E**:
  `decideLean` rejects `saysBind` (`lean/DLC/Decidability.lean:836` — "likewise
  fail-closed for says-E"; :2161; and the note at :308–315 flags this as the
  "Lean/Rust gap"). `PropDeriv` has a `letSaysE` constructor but **no `saysE`
  constructor** (its induction, `progress_aux`, has a `letSaysE` case at
  `Progress.lean:236` and none for `saysE`). So a well-typed `saysBind` never
  arises in the Progress fragment; freezing its reduction cannot break Progress.
- **Subject reduction** (`propDeriv_subject_reduction`,
  `lean/DLC/Decidability.lean`) likewise dispatches `saysBind` via "decideLean
  rejects it → hypothesis false" (:836, :2161). It does not depend on `step`
  reducing `saysBind`.
- **No non-vacuity witness** pins `step (saysBind …)` (contrast §3's T4 witness).

**What DOES break if `saysBind` is frozen:** proof *scripts* — not statements —
that pattern-match the `saysBind` reduct. The closedness-preservation lemma in
`lean/DLC/NonInterferenceEnv.lean:881–903` does `unfold step … split at h` and
handles both says-extract-β and ξ-letsays reducts; freezing `saysBind` would
require rewriting that case to the vacuous/frozen form (step returns `none`, so
`h : none = some M'` is a contradiction). `lean/DLC/ObligationSoundness.lean`
recurses `pendingObligations` through `saysBind` (:77) and cases on it (:359,
:593), and `DerivClosed`/`NonInterferenceTwoRun`/`Subst` case on the constructor
structurally — but those are about the *term shape*, not about `step` firing,
and hold whether or not `saysBind` reduces. All such breakage is mechanically
repairable and weakens no theorem.

**Net:** says-extract-β(`saysBind`) is a **spec-fidelity / correspondence**
matter, not a load-bearing one. Under **(b)** it could be deleted from the model
without collapsing any of the four theorems — but only because the mechanized
fragment does not yet exercise says-E at all (the fail-closed gap), which is a
known limitation, not evidence that says-E should be inert.

---

## 3. Is discharge-β load-bearing? (experiment 3)

**Finding: discharge-β IS load-bearing. Freezing it is a hard compile break and
reverts T4 to vacuous.**

- **`lean/DLC/Witness/T4.lean` breaks at a specific line.** The T4 non-vacuity
  witness contains
  `example : step Redex = some Payload := by simp [step]`
  where `Redex = Term.discharge (Term.boxed Ow Payload Ev) Ev`. If discharge-β
  is removed from `step`, `step Redex = none` and this `example` fails to
  elaborate. The ledger gates T4's `proven*` status on this witness module
  building (`scripts/ledger.sh`; the witness file's own header says so).
- **Three proofs regain vacuous discharge cases.** Commit `9518b2d` (which
  *added* discharge-β) states it "invalidated three proofs that had discharged
  their case with 'frozen — vacuous'. All three now carry real content":
  subject reduction (`Decidability.lean`), closedness preservation
  (`NonInterferenceEnv.lean`), and T4 itself
  (`ObligationSoundness.lean::t4_no_new_obligation`, whose discharge case became
  "the interesting one — the redex DESTROYS a box"). Option (b) returns all
  three to vacuous.
- Note the asymmetry with §2: `PropDeriv` **does** admit `discharge`
  (`decideLean` accepts it; `Decidability.lean:~2178` builds `PropDeriv.discharge`),
  even though its introduction form `boxed` is fail-closed until R5. That is why
  the discharge β-case is *provably unreachable* in the propositional fragment
  yet the redex is still exercised by the full-`Deriv` T4 witness.

---

## 4. One-shot / replay analysis — does discharge-β conflict with one-shot declassification? (the crux)

**Finding: no conflict. The premise that freezing `discharge` protects a
one-shot property does not hold in this calculus. Two distinct things are being
conflated.**

1. **`Discharge` ≠ `Declassify`.** They are different constructors with
   different jobs:
   - `Declassify(Label, Term, Term)` is the IFC declassification form
     (`spec/typing-rules.md` §7, rule at :144; `Deriv.declassify`
     `Judgment.lean:239`). **It is frozen in BOTH the model and the runtime**
     (`Reduce.lean:154`, `reduce.rs:129`). There is *no* model/runtime
     divergence on declassification. The nucleus one-shot-declassification
     design (Ed25519-keyed `DeclassificationToken`, non-replayable — recorded in
     the session memory) maps to **`Declassify`**, and on that constructor the
     model and runtime already agree: both freeze it, so there is no
     auto-reducing β-redex to enable replay. The replay worry does not touch the
     disputed rules.
   - `Discharge(Term, Term)` is the eliminator for the **obligation** modality
     `□_O φ` (`spec/typing-rules.md` §8, rule at :163). It has nothing to do
     with IFC label lowering.

2. **`Discharge`'s one-shot property comes from TYPING (linearity), not from
   freezing reduction.** `spec/typing-rules.md:167–169`: "The `discharge` rule
   is the **only** elimination form for `□_O φ`. The side condition 'O is
   linear' enforces the one-shot semantics — an obligation discharged once
   cannot be discharged again." The guarantee is a linear-context side
   condition, checked at typing time; it is independent of whether the reducer
   fires discharge-β.

3. **discharge-β is the mechanism that MAKES discharge one-shot, not a violation
   of it.** `Reduce.lean:130–142` and commit `9518b2d`: the redex *destroys the
   box*, so its obligation "leaves `pendingObligations` exactly once." This is
   precisely the `one_shot_discharge` (R2a) / R5 multiset-accounting property.
   A box is not a repeatable resource: `discharge(box_O(M,N), P) ▷ M` consumes
   the box, and the reduct `M` has no `boxed` head, so it cannot be discharged
   again (`Witness/T4.lean`: `Ow ∈ pendingObligations Redex` before,
   `Ow ∉ pendingObligations Payload` after). Repeated application is impossible
   because there is no second box to match. So "unconditional, repeatable" is a
   mischaracterization: the rule fires *once per box*, and the box is gone.

4. **Freezing `discharge` in the runtime would not provide any one-shot
   guarantee** — it would merely make the runtime unable to *observe* obligation
   consumption via reduction, while the model (and the T4 theorem) account for
   it. If anything, a runtime that never reduces `discharge` is the one out of
   step with the obligation semantics.

**Sub-conclusion:** §4 does not support (b). The security property that the
task worried about (one-shot, non-replayable) lives on `Declassify` (frozen in
both, no divergence) and, for `Discharge`, on the linear typing side condition
(unaffected by reduction). discharge-β reducing is consistent with, and in fact
implements, one-shot discharge.

---

## 5. Provenance — when and why the two arms entered the model, and why the Rust lagged

Timeline (all commits by Brandon; SHAs from `git log`/`git blame`):

- **`a827073`** (2026-07-02, "T3 rung 3b-0 — congruence (ξ) rules in step").
  Touched **both** `Reduce.lean` and `reduce.rs` together. At this commit the
  two reducers were in sync; `letSays` reduced in both; `saysBind` did not yet
  exist; `discharge` was frozen in both.
- **`9518b2d`** (2026-07-20, "discharge-beta — the redex that destroys the box
  (T4 R4)"). A `feat(lean)` commit. Touched `Reduce.lean`, `Decidability.lean`,
  `NonInterferenceEnv.lean`, `ObligationSoundness.lean`, **and
  `spec/typing-rules.md`** — but **not `reduce.rs`**. The spec was moved from
  "discharge-β NOT implemented" to "implemented as of R4"
  (`spec/typing-rules.md:286–300`). Commit body: "`spec/typing-rules.md` has
  said since 2026-07 that discharge-beta 'awaits the obligation-carrying
  constructor'. R1–R3 delivered that constructor, so the rule lands."
- **`bcdfa27`** (2026-07-20, #131, "Term::SaysBind — says-E gets the binder term
  the spec always gave it"). A `feat(core,protocol)!` commit. Added the
  `SaysBind` constructor to `syntax.rs` (wire tag 23), the decoder, model
  exporters, `dlc-verifier`, and the hand Lean `Reduce.lean` says-extract arm —
  but **`git show bcdfa27 -- crates/dlc-core/src/reduce.rs` is empty**: the
  `step` function was never given a `SaysBind` reduction arm. The commit's own
  "Next:" note lists the Lean mirror as follow-up and does not mention updating
  the runtime reducer.

`crates/dlc-core/src/reduce.rs` has not been functionally touched since
`a827073` (its only later commit is `cf36b3e`, a clippy-allow style change). Its
header comment is now **stale**: it still says "discharge-β awaits the
obligation-carrying constructor (T4 non-vacuity package)"
(`reduce.rs:15–16`) — but that constructor (`box_O`) landed in R1–R3 and
unblocked discharge-β in the model and spec. Likewise its frozen-forms comment
still lists `Discharge` (:128).

**Reading:** this is divergence-by-omission. The model and the spec advanced two
redexes (discharge-β on 07-20, saysBind-β on 07-20); the runtime reducer was not
updated to match, and there is **no comment or commit message anywhere stating
that the runtime deliberately freezes these for a semantic or security reason** —
the only rationale on record (the stale `reduce.rs` header) describes a *pending*
state that has since been satisfied. That is the signature of an oversight, not
a design decision. Points to **(a)**.

---

## 6. Prior art

- **DCC — Abadi et al., *A Core Calculus of Dependency* (POPL 1999)** and *Access
  Control in a Core Calculus of Dependency*. `A says` is a **monadic** type
  constructor; its elimination is a monadic bind, and bind is a genuine β-redex
  (`bind (η m) k ▷ k m`) subject to a "protected at ℓ" **typing** side condition.
  The side condition gates *typing*, not *reduction*. This is the direct analogue
  of DLC's says-E: `says`-elimination reduces (says-extract-β); any restriction
  lives in the typing rule, not by freezing the reducer.
  <https://www.cs.cornell.edu/andru/cs711/2003fa/reading/abadi99core.pdf> ·
  <https://users.soe.ucsc.edu/~abadi/Papers/acldcc-acm.pdf> ·
  <https://dl.acm.org/doi/pdf/10.1145/292540.292555>
- **Garg & Pfenning, *Non-interference in Constructive Authorization Logic*
  (CSFW 2006)** and *A Modal Deconstruction of Access Control Logics* (FoSSaCS
  2008). Constructive authorization logic with a `says` modality established via
  **cut-elimination** — i.e. says-elimination normalizes/reduces; it is not a
  gated, inert eliminator. Non-interference is proved on the normalizing system.
  <https://www.semanticscholar.org/paper/Non-interference-in-constructive-authorization-Garg-Pfenning/aec01f9f63e6cb937bdb5e32df288f6c07eb034e> ·
  <https://link.springer.com/chapter/10.1007/978-3-540-78499-9_16>
- **Affine/linear one-shot resources.** In affine and linear systems the
  "use-once" property of a resource is enforced by the **structural typing
  discipline** (no contraction), while reduction (the affine/linear analogue of
  β) freely consumes the resource exactly once. Consistent with DLC's design:
  the box is a linear resource, discharge-β consumes it, one-shot-ness is the
  linear side condition. <https://ncatlab.org/nlab/show/affine+logic> ·
  <https://en.wikipedia.org/wiki/Affine_logic>

**Takeaway from the literature:** the mainstream treatment reduces `says`- and
resource-eliminations as β-redexes and enforces any "who/when/once" restriction
in the *typing* rule. That matches the DLC model (reduce, gate in typing), not a
runtime that freezes the eliminators.

---

## 7. What breaks if we fix Rust (experiment 6)

Ran directly in the worktree (Rust is cheap). Added two arms to `reduce.rs`
mirroring the model: `SaysBind` copied from the `LetSays` arm; `Discharge` as
`discharge(Boxed(_,inner,_), _) ▷ inner` with ξ-descent. `subst.rs` already
handles both constructors (`SaysBind` with body cutoff+1 at :100,:198;
`Discharge` at :57,:159), so the arms compile without further plumbing.

- `cargo build -p dlc-core`: clean.
- `cargo test -p dlc-core`: **49 passed, 0 failed.** No test asserts that
  `SaysBind`/`Discharge` freeze (`grep` for such a test is empty; the one frozen
  test, `frozen_scrutinee_is_stuck`, uses `LetSays` over an `Attenuate` and is
  unaffected).
- `cargo clippy -p dlc-core`: clean (the `manual_map` allow already covers the
  match shape).
- `cargo test --workspace`: **all crates green** — `dlc-verifier` 33 tests,
  `dlc-protocol`, `dlc-crypto`, `dlc-bench`, CLI, wasm — 0 failures.

The change was reverted; nothing is committed.

**Caveat (not exercised here):** option (a) is only *complete* once the Aeneas
translation `lean/DLC/Aeneas/DlcCore` is regenerated from the fixed `reduce.rs`
and the drift gate (`scripts/check-drift.sh`) is green. That regeneration was
**not** run — Aeneas regen in this ecosystem is currently blocked by a
~3-month-stale Charon/Aeneas toolchain (recorded separately), and it is a
CI-artifact step. Importantly, the *direction* is convergent, not divergent: the
hand-written `lean/DLC/Reduce.lean` already reduces both `SaysBind` and
`Discharge`, so regenerating Aeneas from the fixed Rust brings the *generated*
Lean into agreement with the *hand* Lean and closes the R2 correspondence — which
is the entire point of the fix. (A live nucleus interaction check was out of
scope: nucleus is an upstream path dep and must not be modified from this
workspace; the reverse-dependency guard in nucleus CI is about
`canonical_edge_bytes` wire shape, which `reduce.rs` does not touch.)

---

## 8. Recommendation

**Recommend (a) FIX RUST**, with one honest nuance on scope.

**Confidence: high (≈0.9)** for `Discharge`; **high for the direction, moderate
on urgency** for `SaysBind`.

**Single most decisive piece of evidence:** the **spec is the source of truth
and the spec already mandates both reductions**, and the Rust runtime is simply
behind it. `spec/typing-rules.md:286–300` records discharge-β as "IS implemented
as of R4," and §4/§11 give says-E (`saysBind`) the says-extract reduction — both
changes landed in the spec + model in commits `9518b2d` and `bcdfa27`, and
`reduce.rs` was never updated (empty diff on `bcdfa27`; stale
"awaits the … constructor" header). Per `CLAUDE.md` the spec is updated first and
the Rust mirrors it; here the mirror lagged. Fixing Rust restores the intended
model = spec = runtime alignment. Fixing the model would instead delete a rule
the spec explicitly says is implemented, silently re-introduce vacuity into T4
(§3), and put DLC at odds with the standard DCC / Garg–Pfenning treatment of
`says`-elimination (§6).

**Why the nuance.** The two rules are not equally forced:
- **`Discharge` — fix Rust, load-bearing.** Freezing it in the model breaks
  `Witness/T4.lean` and reverts three proofs to vacuous (§3). The runtime must
  reduce it for T4's non-vacuity to mean anything about running code.
- **`SaysBind` — fix Rust for correspondence/spec-fidelity, but it is not
  load-bearing today** (§2): the mechanized Progress/subject-reduction fragment
  is fail-closed on says-E, so neither freezing it in the model nor adding it to
  Rust changes any of the four theorems *right now*. The correct fix is still to
  add it to Rust (it is the spec's canonical says-E, it is operationally
  identical to `letSays` which already reduces, and `Deriv.saysE` types it), but
  the author could reasonably sequence it after `Discharge` and pair it with
  finally lifting the `PropDeriv` says-E fail-closed gap noted at
  `Decidability.lean:308–315`.

**The case for (b), stated fairly.** If the author's intent were that `SaysBind`
and `Discharge` be *verifier-gated* forms (checked by the `⊢_K`/IFC/obligation
layers, computed only after an out-of-band authorization step) rather than free
β-redexes — the way `Verify`, `Attenuate`, and `Declassify` are — then the
runtime freeze would be the intended design and the model's unconditional
β-rules would be the over-eager simplification. This memo found **no evidence for
that intent**: the spec says the opposite for both rules, no comment or commit
records a deliberate freeze, and the one-shot property the freeze might protect
is (for `Discharge`) already carried by the linear typing side condition and
(for `Declassify`, the actual one-shot-declassification form) already frozen in
both model and runtime. Absent such intent, (b) weakens the artifact.

---

*Investigator note: experiments 2 and 3 were assessed by reading the exact proof
obligations and the T4 witness rather than by a cold multi-hour Mathlib/Aeneas
rebuild; the discharge-β break is a guaranteed elaboration failure at a named
`example`, and the saysBind non-load-bearingness follows from the documented
fail-closed says-E fragment plus an empty search for any witness pinning
`step (saysBind …)`. Experiment 6 was run in full. All experimental edits were
reverted; nothing is committed.*
