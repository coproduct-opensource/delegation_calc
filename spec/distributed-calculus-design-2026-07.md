# DLC-D Phase R1 — First-Classing the Distributed Constructs (DESIGN PROPOSAL)

**Status:** DESIGN PROPOSAL for review. This document proposes, but does **not**
implement, an extension of the DLC calculus that first-classes the distributed
constructs currently living as wrappers over `DLC.Term` in `lean/DLCD/*.lean`.
Nothing here is proven yet; every new theorem below is stated as **proposed / to
be proved**. No `spec/syntax.md`, `spec/typing-rules.md`, `.rs`, or `.lean` file
is edited by this proposal — those are the lockstep implementation step, gated on
approval of this design.

**What this closes.** Today the distributed layer models a command as a *host-language
structure* `DLCD.Rsm.Command { payload : Term, cap : Option Prop' }` and gates the
controlled operation (committing a write) behind a *side-condition* — the
`Authorized`/`WellFormedLog` predicate that `commit` takes as a required Lean
argument (`lean/DLCD/CapSafety.lean`). The four DLC-D guarantee classes G1–G4 are
proven **about that model** (`status = "proven"` for the `DLCD_*` keys in
`lean/theorem-status.json`; the honest fences are recorded in
`spec/distributed-guarantees.md`). This proposal makes the command a **term of the
calculus** and the authorization gate a **typing rule**, so that "only a
`says`-holder may commit a write" is discharged by the type system's own inversion
rather than by an out-of-band provenance predicate — and re-founds G1–G4 onto the
first-classed constructs rather than re-proving them from scratch.

**Realizability contract.** Every proposed constructor below maps to a concrete
`Term`/`Prop'` addition consistent with the existing `DLCD.Rsm` operational model
(`applyCommand`, `worldStep`, `commit`) and the DLCD guarantees. Where a change
would force an existing guarantee to be re-proved from scratch (rather than
re-founded onto the new constructor), it is flagged **[RE-PROVE]**; where the
existing proof re-founds with a case addition, it is flagged **[RE-FOUND]**.

---

## 0. Prior art (web-searched 2026-07-22; URLs recorded)

The design problem — *adding effectful/command constructs to a typed calculus,
gating them by a capability as a typing rule, and threading a resource budget as a
grade* — has direct, load-bearing prior art. This is not a research gamble; the
shapes are known-good.

### First-classing an effectful/command construct as a typed term
- **Moggi, _Computational λ-calculus and monads_** — the foundational
  value/computation distinction: a computation over `A` gets a monadic type `T A`,
  isolating effects in the type. Our `Command`/`Replicated` are the DLC analogue of
  `T φ` (a committed computation over store-type `φ`).
  <https://www.semanticscholar.org/paper/Computational-lambda-calculus-and-monads-Moggi/f67dec0099505e23e9441a9a567fea1d97ff69f6>
- **Brachthäuser, Schuster, Ostermann, _Effects as Capabilities_ (OOPSLA 2020)**
  and **Effekt / System C** (_Rows and Capabilities as Modal Effects_, arXiv 2025):
  a capability-based effect system where a computation's type records which
  *capabilities it requires from its context*, and the typing judgement carries an
  explicit capability set. This is exactly our `commit-I`: a command is well-typed
  only against a capability credential it demands.
  <https://dl.acm.org/doi/10.1145/3428194>,
  <https://arxiv.org/pdf/2507.10301>,
  <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A19680B18FB74AD95F8D83BC4B097D4F/S0956796820000027a.pdf/effekt_capabilitypassing_style_for_type_and_effectsafe_extensible_effect_handlers_in_scala.pdf>
- **Boruch-Gruszecki et al., _Tracking Captured Variables in Types_** and the
  capture-calculus line: capabilities threaded through types rather than a separate
  monitor. <https://arxiv.org/pdf/2105.11896>

### Capability-gated operation as a typing rule (`says`-indexed)
- **Abadi, _Access Control in a Core Calculus of Dependency_ (POPL 1999 CCD /
  ACLDCC)**: `p says φ` as a principal-indexed (idempotent) monad — the protected
  operation is reachable only through the modality. `commit-I`'s premise
  `⊢ cred : issuer says capProp` is the CCD-monad discipline made a commit gate.
  <https://users.soe.ucsc.edu/~abadi/Papers/acldcc-acm.pdf>
- **Garg & Pfenning, _Non-Interference in Constructive Authorization Logic_
  (CSFW 2006)** — the `says` affirmation modality as a modal enrichment of *linear*
  logic, the theoretical warrant for the linear `CDerivS` credential.
  <https://people.mpi-sws.org/~dg/papers/csfw06.pdf>
- **Bauer, _Proof-Carrying Authorization_** — the requester submits a proof that
  policy authorizes the request; the monitor checks it. `commit-I` internalizes
  the proof as a term subterm. <http://users.ece.cmu.edu/~lbauer/papers/thesis.pdf>
- **Bowers, Bauer, Garg, Pfenning, Reiter, _Consumable Credentials in
  Linear-Logic-Based Access Control_ (NDSS 2007)** — the linear (single-use) reading
  the `FailureBudget`-as-grade design foreshadows.
  <http://users.ece.cmu.edu/~lbauer/papers/2007/ndss2007-consumable.pdf>

### `FailureBudget` / `Converges` as a graded/quantitative type
- **Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, _Combining Effects and
  Coeffects via Grading_ (ICFP 2016)** — the semiring-graded framework the
  budget-grade instantiates. <https://cs-people.bu.edu/gaboardi/publication/GaboardiEtAlIicfp16.pdf>
- **Orchard, Liepelt, Eades, _Quantitative Program Reasoning with Graded Modal
  Types_ (Granule, ICFP 2019)** and **_On Graded Coeffect Types for Information-Flow
  Control_** — graded modal types as consumable resource grades.
  <https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf>,
  <https://granule-project.github.io/papers/security-coeffects-mycroftfest.pdf>
- **_Resource-Bounded Type Theory: Compositional Cost Analysis via Graded
  Modalities_ (arXiv 2025)** — a budget carried and consumed by a graded modality,
  the exact `FailureBudget` shape. <https://arxiv.org/pdf/2512.06952>
- **McBride, _I Got Plenty o' Nuttin'_ (2016)** and **Atkey, _QTT_ (LICS 2018)** —
  the usage-vector context the CARVe judgment (`DLC.CarveCtx`) already realizes,
  into which the budget grade threads. <https://bentnib.org/quantitative-type-theory.pdf>

### `Replicated φ` / `Converges φ` — a convergence modality
- **Kaki, Priya, Sivaramakrishnan, Jagannathan / Liu et al., _Type-Checking CRDT
  Convergence_ (PLDI/OOPSLA 2023)** — a type system whose types carry the
  convergence obligation of a replicated datatype; `Converges φ` is the DLC analogue.
  <https://dl.acm.org/doi/abs/10.1145/3591276>
- **Gomes, Kleppmann, Mulligan, Beresford, _Verifying Strong Eventual Consistency_
  (OOPSLA 2017, Isabelle/HOL)** — the abstract-convergence order-relation core that
  `DLCD.Calm` already mirrors; `Converges φ` reflects it into the type.
  <https://martin.kleppmann.com/papers/crdt-isabelle-oopsla17.pdf>
- **Shapiro, Preguiça, Baquero, Zawirski, _Conflict-Free Replicated Data Types_
  (SSS 2011)** — CvRDT convergence = join on a semilattice.
  <https://link.springer.com/chapter/10.1007/978-3-642-24550-3_29>
- **Mondal, Algehed, Arden, _FLAQR_ (CSF 2022)** — a core calculus for distributed
  apps with quorum replication and consensus whose noninterference theorems
  characterize confidentiality/integrity/availability; the closest calculus-level
  prior art for first-classing distribution. <https://arxiv.org/abs/2205.04384>

### The DLC extension procedure this proposal must obey
`CLAUDE.md` "When extending the calculus": (1) `spec/syntax.md` + `spec/typing-rules.md`
first, (2) mirror in `dlc-core/src/{syntax,judgment}.rs`, (3) mirror in
`lean/DLC/{Syntax,Judgment}.lean`, (4) `scripts/check-drift.sh` (Aeneas regen),
(5) update every affected theorem; a break is a real result to be discussed, never
silently weakened. The original DLC-D plan's "~15 files, ~6 inductions" cost model
is the yardstick §5 uses.

---

## 1. New `Term` constructors — `command` and `query`

### 1.1 The current object being first-classed

`lean/DLCD/Rsm.lean`:

```
structure Command where
  payload : Term              -- the operation, applied to the replica's store
  cap     : Option Prop' := none   -- guarding capability / IFC label (opaque in 1.0)

def applyCommand (c : Command) (s : Term) : Term :=
  (reduceWithFuel (Term.app c.payload s) applyFuel).1
```

A command is *operationally* just "apply `payload` to the store and normalize". The
`cap` slot is opaque at the operational layer; `CapSafety.lean` makes it load-bearing
only through the `Authorized` side-condition on `commit`. First-classing = turning
this host-structure into a `Term` constructor whose **well-typing** carries the
authorization, and whose **reduction** reproduces `applyCommand`.

### 1.2 Proposed constructors (exact shapes)

Rust (`crates/dlc-core/src/syntax.rs`, appended to `enum Term`):

```rust
/// `command(M, c, ℓ)` — a first-class replicated write. `M` is the store
/// transformer (`φ ⊸ φ`); `c` is the capability credential term proving
/// `issuer says capProp`; `ℓ` is the IFC label at which the write is classified.
/// Reduces transparently under application (the credential/label are checked at
/// typing, erased at reduction), so `app (command M c ℓ) s` β-reduces to `app M s`
/// — exactly `applyCommand`'s behaviour.
Command(Box<Term>, Box<Term>, Label),
/// `query(V, w)` — a read of a replicated value `V : Replicated φ` accompanied by
/// a convergence witness `w : Converges φ`, yielding `φ @ ℓ`. Reduces to `V`
/// (a read; convergence makes the projection replica-independent).
Query(Box<Term>, Box<Term>),
```

Lean (`lean/DLC/Syntax.lean`, appended to `inductive Term`):

```
| command : Term → Term → Label → Term      -- payload, credential, label
| query   : Term → Term → Term              -- replicated value, convergence witness
```

**Design decisions embedded in the shape** (each has an open question in §7):
- The **credential is a term subterm**, not a typing side-condition. This mirrors
  the `Sign`/`Boxed` discipline (`spec/syntax.md` §5: "the obligation is carried by
  the TERM, not merely by the typing derivation") and is what lets capability-safety
  become an *inversion* on the `command` constructor rather than an audit of a
  separate provenance predicate. See §3.
- **Neither constructor is a binder.** `command` has two subterms (`payload`,
  `cred`), `query` has two (`value`, `witness`); none binds a variable. So — unlike
  `saysBind`/`letTensor` — `shift`/`substAt` recurse into the subterms **without
  bumping the cutoff**. This is the cheapest possible substitution interaction (the
  `App`/`Pair` shape, not the `Lam`/`saysE` shape), a deliberate cost choice.
- The `Label` on `command` is a first-class field (like `Term.liftLabel`), so the
  write's IFC classification is syntactic and the distributed-NI store type
  `Prop'.at χ ℓ` (`DLCD.DistributedNI`) is recoverable from the term.

### 1.3 Proposed reduction (consistent with `applyCommand`)

`spec/typing-rules.md` §11, appended to the redex list (append-only):

```
(command-β)    app (command M c ℓ) s   ▷  app M s        -- credential/label erased
(query-β)      query V w               ▷  V              -- read the replicated value
(ξ-command)    M ▷ M'  ⇒  command M c ℓ ▷ command M' c ℓ  -- normalize the payload
(ξ-query)      V ▷ V'  ⇒  query V w ▷ query V' w
```

`command-β` is the crux of **[RE-FOUND]** for the whole RSM layer: because
`app (command M c ℓ) s` steps in one move to `app M s`, the definition

```
applyCommand c s := (reduceWithFuel (app c.payload s) applyFuel).1
```

is unchanged in *value* when `c.payload` is replaced by a first-class
`command M c ℓ` whose payload is `M` — the extra `command-β` step is absorbed by
`applyFuel` (1024 ≫ 1). So `applyPrefix`, `deliver`, `worldStep`, and the convergence
seed `replicas_converge_on_prefix` re-found with **no change to their statements**,
only the `step`/`step_deterministic`/progress inductions gaining two cases (§5).
The credential and label being *erased at reduction* is what keeps convergence a
function of the payload alone — the authority lives entirely in the typing.

---

## 2. New `Prop'` constructors — `Replicated φ` and `Converges φ`

Lean (`lean/DLC/Syntax.lean`, appended to `inductive Prop'`); Rust mirror in
`enum Prop`:

```
| replicated : Prop' → Prop'      -- Replicated φ : a value replicated across the RSM at store-type φ
| converges  : Prop' → Prop'      -- Converges φ  : the convergence obligation/guarantee at φ
```

### 2.1 `Replicated φ` — what it is and what inhabits it

`Replicated φ` is the **type of a value that has entered the committed replicated
log at store-type `φ`**. It is the type-level shadow of `AppliedPrefix`/the committed
store (`DLCD.Rsm`). It is a **modality applied on commit**, not the store type
itself (see the §7 ruling): a store holds a `φ`; committing a write *about* that
store produces a `Replicated φ`.

- **Introduction:** the `commit-I` rule (§3). A `command M c ℓ` whose credential
  proves the issuer's write capability and whose payload is a `φ`-store-endomorphism
  is typed `Replicated φ`. This is the *only* introduction — mirroring "the only
  ingress to the committed log is `commit`" (`DLCD.CapSafety.mem_commit_authorized`).
- **Elimination:** reading a replicated value back at `φ`, *gated by a convergence
  witness* — the `query`/read rule (§2.2, §3.4). Because all replicas that applied
  the same prefix hold equal stores (`replicas_converge_on_prefix`), a read of a
  `Replicated φ` with a `Converges φ` witness yields a replica-independent `φ`.

### 2.2 `Converges φ` — what it is and what inhabits it

`Converges φ` is the **type of evidence that reads of a `Replicated φ` converge** —
the type-level reflection of `DLCD`'s convergence theorems. It is inhabited by *either*
of the two convergence routes the model already proves:

- **CALM route (`convergesI-monotone`).** If the store-type `φ`'s update algebra is
  monotone (a join-semilattice), `Converges φ` is inhabited *coordination-free*:
  the type-level reflection of `DLCD.Calm.coordination_free_convergence`
  (`DLCD_coordination_free_convergence`, proven). The witness is a proof that `φ`'s
  merge is `⊔` on a semilattice (commutative/associative/idempotent).
- **Consensus route (`convergesI-consensus`).** For the general (non-monotone) case,
  `Converges φ` is inhabited by a total-order/agreement witness: the reflection of
  `DLCD.Consensus.replicas_converge_via_consensus` (`DLCD_replicas_converge_via_consensus`,
  proven) — convergence relative to the discharged committed-log oracle.

`Converges φ` is thus the **proof obligation that a read is deterministic**; it makes
the CALM/consensus *boundary* (`spec/consensus.md`, `DLCD.Calm`'s right-reason bite)
a typing obligation: a read of a non-monotone `Replicated φ` without a consensus
witness is not well-typed.

**Typing of the modalities themselves** (`Prop'` well-formedness): both `replicated`
and `converges` are single-argument modalities; their `Prop'` DecidableEq / inference
cases (`decide.rs`, `Decidability.lean`) recurse into the argument exactly as
`says`/`within` do. No new lattice or principal machinery.

---

## 3. Capability-gated commit as a TYPING RULE — `commit-I`

This is the heart of the proposal: replace the out-of-band side-condition
`Authorized c issuer` / `WellFormedLog` (the Lean argument `commit` demands) with an
**in-calculus typing obligation**.

### 3.1 The additive rule (`Deriv`, `lean/DLC/Judgment.lean`)

`spec/typing-rules.md`, proposed new §13 "Distributed" (append-only, stable index):

```
Γ_A; Γ_L^1 ⊢ c : issuer says capProp        Γ_A; Γ_L^2 ⊢ M : φ ⊃ φ
──────────────────────────────────────────────────────────────────────  (commit-I)
Γ_A; Γ_L^1, Γ_L^2 ⊢ command M c ℓ : Replicated (φ @ ℓ)
```

Lean constructor sketch (`Deriv`):

```
| commitI (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (issuer : Principal)
          (capProp φ : Prop') (ℓ : Label) (M c : Term)
    (dc : Deriv { additive := Γₐ, linear := Γ₁ } c (Prop'.says issuer capProp))
    (dM : Deriv { additive := Γₐ, linear := Γ₂ } M (Prop'.imp φ φ)) :
    Deriv { additive := Γₐ, linear := Γ₁ ++ Γ₂ }
          (Term.command M c ℓ) (Prop'.replicated (Prop'.at φ ℓ))
```

**Premises, read against the current model:**
- `dc : … c : issuer says capProp` is *exactly* the `Deriv Γ capTerm (issuer says
  capProp)` witness that `DLCD.Authorized` existentially demands today — now a
  first-class subterm-derivation instead of a `Nonempty` field.
- `dM : … M : φ ⊃ φ` is the *typed-log invariant* that `DLCD.TypedLog.WellTypedCmd`
  imposes today (`PropDeriv [] payload (imp φ φ)` + `CoreTerm`) — now a premise of the
  same rule, not a separate admission gate.
- The conclusion `Replicated (φ @ ℓ)` fuses the store type and its IFC label, so
  distributed-NI (`DLCD.DistributedNI`, whose store type is `Prop'.at χ ℓ`)
  re-founds directly.

### 3.2 How this replaces the side-condition — capability-safety by inversion

Today: `capability_safety (log) (hwf : WellFormedLog log) : ∀ c ∈ log, ∃ issuer,
Authorized c issuer` — an induction over the *provenance predicate*.

Proposed: capability-safety becomes an **inversion lemma on `commitI`**. If
`Deriv Γ (command M c ℓ) (Replicated (φ @ ℓ))` is derivable, then by inversion its
first premise gives `Deriv … c (issuer says capProp)` — the credential is recovered
*from the typing derivation of the term itself*. The metatheorem (proposed):

```
theorem committed_command_says_cap        -- PROPOSED, to be proved
    (h : Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.at φ ℓ))) :
    ∃ issuer capProp Γ', Nonempty (Deriv Γ' c (Prop'.says issuer capProp))
```

This is **[RE-FOUND]**, not [RE-PROVE]: the content of `capability_safety` (every
committed command carries a `says`-credential) is preserved; it moves from "extract
from provenance chain" to "invert the constructor". The existing `WellFormedLog`
predicate and `capability_safety` theorem can be **retained as a derived corollary**
during migration (a `WellFormedLog` is any log all of whose elements are
`commitI`-typable), so no existing DLCD theorem statement is deleted mid-flight.

### 3.3 The linear interaction — `commit-I-L` lives in `CDerivS`, not `CDeriv`

This is the subtle, load-bearing part and repeats a lesson already learned in
`lean/DLCD/CapSafetyLinear.lean`. `CDeriv` (`DLC.CarveJudgment`) **deliberately has
no `says`-introduction** — adding one breaks `cderiv_subject_reduction'` because
`CDeriv.saysE` *keeps* the modality while `step` *strips* it (the modality mismatch
documented at `CapSafetyLinear.lean:14-38`). The existing fix is the **seal**
`CDerivS` (embed any `CDeriv` + add the linear `saysI`).

`commit-I` introduces a **new modality** (`Replicated`) *and* consumes a `says`
credential, so by the identical argument it **must live in the seal `CDerivS`, not
in `CDeriv`**. Proposed linear rule:

```
CDerivS Γ₁ c (issuer says capProp)     CDeriv Γ₂ M (φ ⊸ φ)     CJoin Γ₁ Γ₂ Γ
────────────────────────────────────────────────────────────────────────────────  (commit-I-L)
CDerivS Γ (command M c ℓ) (Replicated (φ @ ℓ))
```

Lean (extend the existing `CDerivS` inductive in `CapSafetyLinear.lean`):

```
| commitI {Γ₁ Γ₂ Γ : Carve.Ctx Prop'} {M c : Term} {issuer : Principal}
          {capProp φ : Prop'} {ℓ : Label}
    (dc : CDerivS Γ₁ c (Prop'.says issuer capProp))   -- the linear credential (seal)
    (dM : CDeriv  Γ₂ M (Prop'.lolli φ φ))             -- the store endomorphism (CARVe)
    (hj : Carve.CJoin Γ₁ Γ₂ Γ) :
    CDerivS Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.at φ ℓ))
```

- **Context discipline:** the credential's resources `Γ₁` and the payload's `Γ₂`
  join elementwise via `CJoin` (usage-vector addition, `DLC.CarveCtx`) — the
  linear/multiplicative split, mirroring `imp-E`/`tensor-I`. A *linear* (`Mult.one`)
  credential is genuinely consumed by the commit; a `many` credential is reusable.
  This is the "consumable credential" reading (Bowers–Bauer NDSS 2007) made real.
- **Why the seal is mandatory (flag):** because `CDeriv` has no `Replicated`
  introduction and cannot host one without reopening the subject-reduction
  obstruction, `command`/`Replicated` are **CDerivS-only** in the linear world.
  `CDeriv` and its metatheorems (`cderiv_subject_reduction'`, `cderiv_shift`,
  `cderiv_substL`, the L1–L4 line) are **untouched** — the seal never feeds back.
  This is a deliberate scope fence, not a gap: it exactly reuses the 2.c strategy.
- **Additive ↔ linear bridge — honestly deferred.** As with `CDerivS.saysI` today,
  a functorial `Deriv → CDerivS` embedding for `commitI` would need the full
  `Deriv`→CARVe judgment migration (open L4). So the additive `commitI` (§3.1) and
  the linear `commit-I-L` are stated as **corresponding rules**, and their credentials
  correspond shape-for-shape, but a proof that one embeds in the other is future
  work — not claimed here.

### 3.4 The read rule (`query-I`)

```
Γ ⊢ V : Replicated (φ @ ℓ)        Γ ⊢ w : Converges (φ @ ℓ)
──────────────────────────────────────────────────────────────  (query-I)
Γ ⊢ query V w : φ @ ℓ
```

The convergence witness `w : Converges (φ @ ℓ)` is a **required premise** of the read,
so a read of a replicated value is well-typed only when reads are proven
replica-deterministic (via CALM or consensus, §2.2). This internalizes the
`replicas_converge_on_prefix` guarantee as a typing obligation on the reader.
(Whether `query`/`Converges` are in the R1 slice at all is a §7 ruling.)

---

## 4. `FailureBudget` as a linear grade

Today `FailureBudget` (`lean/DLCD/Rsm.lean`) is a plain structure threaded through
`GlobalConfig`, already shaped after `DLC.Graded`'s `DpBudget`
(`zero`/`saturatingAdd`/`le`, plus the enforced predicate `withinContract`). The
proposal threads it as a **consumable grade in the CARVe context**, so that G1–G4
become theorems relative to a *typed* budget rather than a `GlobalConfig` field.

### 4.1 Mirror `Graded.lean`'s `DpBudget` structure

`DLC.Graded` pairs a value with a consumable `DpBudget` grade and proves the
comonad laws (`graded_identity_law`, `graded_associativity_law`) over
`saturatingAdd`. The distributed analogue (proposed `lean/DLCD/FailureGraded.lean`,
or fold into `DLC.Graded`):

```
structure FailureGraded (α : Type) where
  value : α
  grade : FailureBudget          -- the crash-fault grade consumed so far

def pure    (a : α) : FailureGraded α := ⟨a, FailureBudget.zero f⟩
def consume (g : FailureGraded α) (extra : Nat) : FailureGraded α :=
  ⟨g.value, g.grade.saturatingAdd extra⟩          -- charge crash faults, monotone
```

The comonad laws transfer verbatim from `Graded.lean` (`saturatingAdd` on `consumed`
is `Nat`-associative with `zero` as identity), so **[RE-FOUND]** — the grade algebra
is already proven for `DpBudget` and `FailureBudget.saturatingAdd` is the same shape.

### 4.2 Threading the grade through `commit-I`

Two options, ordered by re-proof cost (the §7 ruling picks one):

- **Option A — budget as a graded conclusion modality (strongest, heaviest).**
  Make the commit conclusion carry the grade: `command M c ℓ : Replicated_b (φ @ ℓ)`
  where `b : FailureBudget`, and `commit-I` requires `withinContract b = true` and
  advances the grade (`b' = b.saturatingAdd 1` per tolerated fault). Then G1–G4 are
  quantified over the grade: e.g. convergence holds *provided* the threaded grade
  stays `withinContract`. This makes the failure contract a genuine type index.
  **Cost:** `Replicated` gains a `FailureBudget` argument ⇒ every `Prop'` induction
  (LRel, DecidableEq, inference) touches it. **[RE-PROVE]** for the LRel/NI cases
  (the store type now carries a grade).
- **Option B — budget as a CARVe context resource (lighter, recommended for R1).**
  Add a distinguished budget cell to `Carve.Ctx` (or carry a `FailureGraded`
  wrapper around the whole derivation) and have `commit-I-L` *consume* one budget
  unit via `CJoin`-style accounting, with `withinContract` a side-condition on the
  rule. The grade lives in the context, not the proposition, so `Prop'` inductions
  are untouched and only the CARVe context lemmas (`cjoin_*`) gain a budget
  coordinate. **[RE-FOUND]** onto the existing `CJoin` machinery.

Under either option the deliverable is the same: **the four guarantee classes are
re-stated relative to `withinContract (threaded grade) = true`**, so "these
guarantees hold within the declared crash-fault budget" is a typing fact, not a
`GlobalConfig` field the reader must trust. The existing `FailureBudget.withinContract`
predicate and its use in `DLCD.Witness.SliceWitness` (which already discharges
`budget.withinContract = true`) are the seam this plugs into.

---

## 5. Impact map — files, inductions, per-construct re-proof burden

The DLC extension procedure (`CLAUDE.md`) and the "~15 files, ~6 inductions"
yardstick. Below, per constructor, the files that must change and the inductions
that gain cases. **A Lean `inductive`/`match` with no catch-all forces exhaustiveness**,
so the compiler *enumerates* every missing case — the gate cannot go stale-green; it
goes RED (won't build) until each case is supplied. That is the migration's friend
(§6).

### 5.1 `Term.command` + `Term.query` (the two term constructors)

**Spec:** `spec/syntax.md` §5 (grammar productions), `spec/typing-rules.md` §11
(redexes), §12 (rule index), new §13 (`commit-I`, `query-I`).

**Rust (`crates/dlc-core/src/`):** `syntax.rs` (`+2` `Term` variants), `subst.rs`
(shift/subst: `+2` recursive, **no cutoff bump** — cheap), `reduce.rs` (`command-β`,
`query-β`, `ξ-command`, `ξ-query`), `decide.rs` (inference `+2`), `judgment.rs`
(rule mirror), `crates/dlc-verifier/src/check.rs` (`+2` case-analysis arms).

**Lean (`lean/DLC/`):** `Syntax.lean` (`+2`), `Subst.lean` (`shift`, `substAt`:
`+2` each; **plus every shift/subst lemma** — `shift_shift`, `subst_shift`,
`closedAbove_*` — gains 2 cases; the *cheap* App-shape, not the Lam-shape),
`Reduce.lean` (`step`: `+2` redex + `+2` congruence), `ReduceMeta.lean`
(`step_deterministic`, `value_steps_eq`, `steps_semiconfluent`: `+2` each),
`Judgment.lean` (`Deriv.commitI`, `Deriv.queryI`), `Decidability.lean`
(type-inference `+2`, `propDeriv_substAt` `+2`, the function-correspondence theorem),
`Progress.lean` (`+2` — a `command`/`query` is a value or steps),
`DerivClosed.lean`, `CtxWellFormed.lean` (`+2` each).

**Inductions that gain cases (term side):** `shift`/`substAt` (+all their lemmas);
`step`/`step_deterministic`; `Deriv`/`PropDeriv`(+`CDerivS`); `pendingObligations`
(`ObligationSoundness.lean` — a `command`/`query` carries no obligation, so the two
cases return `[]`, but the case is *mandatory*); type-inference (`Decidability`);
progress; the two-run relation's *term* cases in `fundamental`.

**Per-construct re-proof estimate:** the two term constructors are the *App-shaped*
(non-binder) additions, the cheapest class. Estimate **each ≈ 1.0–1.5 person-weeks**
of proof engineering, dominated not by the redex (small) but by the **fan-out across
every shift/subst lemma and every `Deriv`-induction metatheorem** — this is the
irreducible "one constructor touches every totality-by-cases function" tax the L1
work already measured. `query` is cheaper than `command` (`query-β` erases to a
subterm; no credential/label bookkeeping).

### 5.2 `Prop'.replicated` + `Prop'.converges` (the two prop constructors)

**Spec:** `spec/syntax.md` §4 (proposition grammar), `spec/typing-rules.md` §13.

**Rust:** `syntax.rs` (`+2` `Prop` variants), `decide.rs` (`Prop` inference /
DecidableEq `+2`), `check.rs`.

**Lean:** `Syntax.lean` (`+2` `Prop'`), and — the expensive part — **the `LRel`
logical relation** (`NonInterferenceLR.lean`): `LRel ℓ (Replicated (φ@ℓ)) M N` and
`LRel ℓ (Converges (φ@ℓ)) M N` must be *defined*, and every lemma that inducts over
`Prop'` gains 2 cases: `lrel_symm`, `lrel_self`/`fundamental`
(`NonInterferenceFundamental.lean`), `lrel_expand`/anti-reduction, **and
`DLCD.DistributedNI`'s `lrel_step_left`/`lrel_step_right`/`lrel_reduce`** (the
forward-closure induction over `Prop'`).

**The design crux (flag).** The `LRel` definition for `Replicated` decides whether NI
is **[RE-FOUND]** or **[RE-PROVE]**. Proposed:
`LRel ℓ (Prop'.replicated φ) M N := LRel ℓ φ (readOf M) (readOf N)` — a replicated
value is low-related iff its underlying `φ`-read is (convergence collapses replicas to
one observable value). With this definition the `Replicated` case *reduces to the
existing `φ` case* → **[RE-FOUND]**. `LRel ℓ (Converges φ) M N := True` (a
convergence witness is proof-irrelevant to a low observer) → trivially [RE-FOUND].
If instead `Replicated` were given independent relational content, the fundamental
lemma's `commitI`/`queryI` cases would be **[RE-PROVE]** from scratch. **Recommend the
collapsing definition.**

**Per-construct re-proof estimate:** **each ≈ 1.5–2.0 person-weeks**, dominated by the
`LRel`/`fundamental` fan-out (T3-noninterference is `proven_fragment`; adding a
`Prop'` case reopens every clause of that induction). The collapsing `LRel`
definition is what keeps this at re-found cost; without it, budget 3–4 weeks and a
genuine new noninterference argument.

### 5.3 The DLCD re-founding (the guarantee modules)

Each of these currently proves a `DLCD_*` guarantee about the *wrapper* `Rsm.Command`;
after first-classing, each must be re-founded onto `Term.command`:

- `Rsm.lean` — migrate `Command`→`Term.command`; `applyCommand`/`worldStep`/seed
  **[RE-FOUND]** (§1.3).
- `CapSafety.lean` / `CapSafetyLinear.lean` — `Authorized`/`commit`/`WellFormedLog`
  re-expressed as `commitI` inversion (§3.2/§3.3); retain old predicates as derived
  corollaries during migration.
- `DistributedNI.lean` / `TypedLog.lean` — the typed-log `htyped` invariant is now a
  `commitI` premise; **[RE-FOUND]** given the collapsing `LRel` (§5.2).
- `Linearizable.lean`, `Consensus.lean`, `MultiDecree.lean`, `Calm.lean`,
  `Termination.lean`, `MultiDecreeLiveness.lean` — statements chain into the
  convergence seed, which re-founds; each gains at most the new `Term.command`
  spelling. **[RE-FOUND]**.
- `Summary.lean` (name-drift tripwire), `Witness.lean` (`SliceWitness` joint
  witness — must be re-exhibited on a `Term.command` execution).

**Aeneas + gates:** `lean/DLC/Aeneas/*` regenerated (`scripts/check-drift.sh`),
`lean/expected-axioms/*.txt` snapshots regenerated per new theorem,
`lean/theorem-status.json` gains entries (`commitI_typing`, `Replicated_*`, etc.,
initially `open`→`proven` as each lands). `scripts/check-spec-drift.sh`,
`scripts/check-axioms.sh`, `scripts/check-tautologies.sh` must stay green.

### 5.4 Rollup

| Change | Files touched | New inductions/rules | Re-proof estimate |
|---|---|---|---|
| `Term.command` | ~14 (spec×2, rust×5, lean×7) | commitI; +cases in shift/subst/step/progress/pendingObligations | 1.0–1.5 wk |
| `Term.query` | ~12 | queryI; +cases (query-β cheaper) | 0.75–1.0 wk |
| `Prop'.replicated` | ~8 | LRel/fundamental +case (collapsing) | 1.5–2.0 wk |
| `Prop'.converges` | ~7 | LRel +case (`True`); convergesI intro | 0.75–1.0 wk |
| `commit-I` / `commit-I-L` | Judgment + CapSafety(+Linear) | inversion metatheorem re-found | 1.0–1.5 wk |
| `FailureBudget` grade | Graded + CarveCtx + Rsm | comonad laws re-found; Option B | 1.0–2.0 wk |
| DLCD re-founding | ~10 DLCD modules + Aeneas + snapshots | all [RE-FOUND] | 1.5–2.5 wk |

**Total honest estimate: ~7–11 person-weeks (multi-week, several increments).**
R1 is not a one-shot change; it is a staged program (§6). The dominant cost is not
any single rule but the **fan-out tax** — every `Term`/`Prop'` constructor addition
reopens every totality-by-cases function and every structural-induction metatheorem,
exactly as `CLAUDE.md`'s "~6 inductions" warns.

---

## 6. Migration strategy — staying green mid-flight

The constraints: keep the DLCD axiom-snapshot gates green, keep every `proven`
theorem `proven` at each step, never let `check-claims.sh` overclaim, and honor
append-only `RuleName` with stable indices.

### 6.1 Append-only, stable indices
New rules `commit-I`, `commit-I-L`, `query-I`, `replicated-I`, `converges-I` are
**appended** to `spec/typing-rules.md` §12's rule index and a new §13; no existing
rule ID moves. New `Term`/`Prop'` variants are appended at the *end* of the
`inductive`, so existing constructor positions (hence Aeneas output ordering) are
stable — minimizing `check-drift.sh` churn.

### 6.2 The compiler enforces the gate — no stale green
Because DLC's `step`, `shift`, `substAt`, `pendingObligations`, `LRel`, and every
`Deriv`-induction use **exhaustive matches with no catch-all**, adding a constructor
makes those files *fail to compile* until every case is supplied. There is no path
where the axiom gate reads green while a case is silently missing — the build is RED
until the induction is complete. (Contrast the pitfall in
`lean-error-grep-misses-paren-form`: here we rely on the *build*, not a grep.)

### 6.3 Staged, construct-by-construct
- **Stage A — `Term.command` + additive `commit-I` + `Replicated`, wrapper retained.**
  Add the constructor and rule; keep `Rsm.Command` as a thin alias
  (`def Command.toCommandTerm : Command → Term`) so all existing DLCD modules still
  compile. Prove `committed_command_says_cap` (inversion) and show it *implies* the
  old `capability_safety`. At the end of Stage A, every prior `DLCD_*` theorem is
  still `proven` (they still speak of `Rsm.Command`); the new inversion theorem is a
  *new* `proven` entry. Nothing regressed.
- **Stage B — migrate the operational layer.** Re-express `applyCommand`/`deliver`/
  `worldStep` on `Term.command`; re-found the convergence seed and `DistributedNI`
  (collapsing `LRel`). Retire `Rsm.Command` once no module references it. The
  `SliceWitness` (`Witness.lean`) is re-exhibited on a first-class execution — this
  is the load-bearing anti-vacuity check that the migration didn't hollow anything.
- **Stage C — the linear seal.** Add `CDerivS.commitI` (`commit-I-L`) and the linear
  capability-safety re-founding, `CDeriv` untouched (§3.3).
- **Stage D — `Query` + `Converges` (if in scope, §7).** Cheapest last.
- **Stage E — `FailureBudget` grade (Option B).** Thread the grade; re-state G1–G4
  relative to `withinContract`.

Each stage is a self-contained PR that lands with its own axiom snapshot and leaves
all gates green; a stage that breaks a `proven` theorem is a *real result* to
surface (per `CLAUDE.md` step 5), never a silent weakening.

### 6.4 `check-claims.sh` discipline (this doc and the work)
This document lives under `spec/`, so `check-claims.sh` scans it. Every new theorem
is written as **proposed / to be proved**; the *existing* `DLCD_*` guarantees are
described as `proven` **about the model** (matching `theorem-status.json`), never as
runtime facts, and the T1–T4 status words are left at their ledger values
(`proven_fragment`/`stated`). No complexity bound, no "four … theorems … mechanized",
no EasyCrypt-discharge claim appears here.

---

## 7. Open design questions (need a ruling before implementation)

1. **`Command` as a `Term` constructor vs. a top-level configuration form.**
   First-classing as a `Term` (this proposal) lets commands be built, delegated,
   attenuated, and nested compositionally — the *stronger* path — but pays the full
   fan-out tax across every `Term` induction. The alternative: keep `Command` a
   top-level form that only ever appears in the log (never nested in a proof term),
   adding a *typing judgment for logs* instead of a `Term` constructor. That is
   cheaper (Term inductions untouched) but forfeits compositional commands.
   **Recommendation:** `Term` constructor (default-to-stronger), but this is the
   single biggest cost lever — ruling requested.

2. **Is `Query`/`Converges` in the R1 slice?** G1–G4 are about *writes* and
   *convergence of the store*; reads can be modeled by store projection without a
   `query` term at all. Proposal: **defer `Query`+`Converges` to R1.b** unless a
   *read-determinism typing guarantee* (a read of a non-monotone replicated value is
   ill-typed without a consensus witness) is explicitly in R1 scope. Ruling requested.

3. **Does `Replicated φ` subsume the store type, or is it a modality applied on
   commit?** Proposal: **modality** — the store holds `φ`, committing produces
   `Replicated φ`. The alternative (every store is `Replicated φ`) is simpler but
   conflates "a value" with "a committed value" and forces `Replicated` into every
   store-typed position. Ruling requested.

4. **Credential as a term subterm vs. a typing side-condition.** Proposal:
   **term subterm** of `command` (proof-carrying; enables capability-safety by
   inversion, matches the `Sign`/`Boxed` annotation discipline). The alternative
   (credential stays a `Deriv` side-condition à la today's `commit`) keeps the `Term`
   surface smaller but forfeits inversion. Ruling requested.

5. **`FailureBudget` grade: Option A (graded conclusion modality) vs. Option B
   (CARVe-context resource) vs. status-quo (`GlobalConfig` field + side-condition).**
   Proposal: **Option B for R1** (lighter, re-founds onto `CJoin`), with Option A
   as an R2 ambition. Ruling requested on how heavy to go.

6. **`commit-I` conclusion — `Replicated (φ@ℓ)` vs. `issuer says (Replicated (φ@ℓ))`.**
   Should the committed value retain the affirmation modality (so a reader sees *who*
   committed), or is the credential's authority discharged at commit? Proposal:
   discharge at commit (conclusion is bare `Replicated`), with the issuer recoverable
   by inversion for audit. Ruling requested.

7. **Which judgment(s) host `commit-I` — additive `Deriv`, linear `CDerivS`, or
   both?** Distributed-NI currently rides `PropDeriv` (additive core); capability
   consumption wants the linear seal. Proposal: **both** — additive `Deriv.commitI`
   for the NI/store-endomorphism story, linear `CDerivS.commitI` for consumable
   credentials — with the `Deriv↔CDerivS` bridge honestly deferred (§3.3). Ruling
   requested on whether R1 must deliver both or may ship the linear seal alone.

---

## 8. Realizability summary (the gate)

Every proposed constructor maps to a concrete addition consistent with the model:

| Construct | Maps to | Operational consistency | NI/guarantee consistency |
|---|---|---|---|
| `Term.command M c ℓ` | `Rsm.Command` first-classed | `command-β ▷ app M s` = `applyCommand` | store type `φ@ℓ` = `DistributedNI` |
| `Term.query V w` | a read | `query-β ▷ V` | gated by `Converges` |
| `Prop'.replicated φ` | committed-store type | intro = `commit-I` | `LRel` collapses to `φ` [RE-FOUND] |
| `Prop'.converges φ` | convergence obligation | reflects `Calm`/`Consensus` theorems | `LRel = True` [RE-FOUND] |
| `commit-I` | replaces `Authorized`/`WellFormedLog` gate | credential erased at reduction | capability-safety by inversion [RE-FOUND] |
| `FailureBudget` grade | `GlobalConfig.budget` internalized | monotone `saturatingAdd` | G1–G4 relative to `withinContract` |

**Nothing here forces a guarantee to be re-proved from scratch, provided the
collapsing `LRel` definition for `Replicated`/`Converges` (§5.2) is adopted.** The
one genuine [RE-PROVE] risk is Option A of the budget grade (§4.2) putting a grade
into the proposition, which reopens the `LRel`/`fundamental` induction with real new
content — hence the recommendation of Option B for R1.

**Honest cost.** R1 is a multi-week, multi-increment program (~7–11 person-weeks,
§5.4), dominated by the fan-out tax of constructor addition, not by any single rule.
The design is realizable and re-founds the existing DLC-D guarantees; it is not a
one-commit change and should not be scheduled as one.
