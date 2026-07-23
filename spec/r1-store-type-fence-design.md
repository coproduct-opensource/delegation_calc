# R1 — Closing the DLC-D "store-type-change" fence: type-track the replicated store's IFC label via ⊔-join through the fold

**Status:** DESIGN PROPOSAL (doc only; no `.lean`/`.rs` edits). Gated on ruling.
**Branch:** `dlc-d/phase0-carve` (HEAD `f37face`).
**Scope:** propose a guarantee-preserving way to make the committed store's IFC
classification **type-tracked through the command-application fold** — turning the
disclosed open fence *"the committed store is a fixed `Term`; a richer store type
is future work"* (`Summary.lean` §"Honest OPEN fences"; governed on
`DLCD_single_linearization`, `DLCD_distributed_noninterference`) into a **theorem**
rather than an assumption — **without** re-proving convergence / NI /
linearizability from scratch.

**One-line verdict (see §6):** the join-label model is the correct design and is
**realizable additively** (existing Term-level proofs untouched), because the
accreted label is a **public, deterministic, monotone parallel fold** that
composes as a *product* with the existing store fold. But its value is **modelling
completeness (per-write taint accretion), not a new security theorem** — the
accreted label carries zero confidentiality content (it is a function of the
*public* committed log, not of secret store contents). Recommendation: **DO the
minimal standalone label-algebra metatheorem now** (~1 additive file, closes the
fence's hard questions definitively and is genuinely non-vacuous); **DEFER** the
invasive `Replica`/`runCmd` fusion. Gating precondition: a real per-command label
source (inc4 Open Q4).

---

## 0. Prior art (web-searched 2026-07-23; URLs recorded)

The recommended model — **a single "current" store label that floats upward by
join (⊔ = least upper bound) on each write, bounded, idempotent** — is not a
novelty; it is the canonical *floating-label* / *coarse-grained dynamic IFC*
discipline, and its convergence half is the standard *join-semilattice CRDT*
argument. The two are literally the same algebra viewed from two fields.

**Floating label = a single current label that joins upward (THE model, option a).**
- **LIO (Labeled IO)** — Stefan et al. LIO associates **one "current"
  floating-label** with a computation; *"when an LIO computation with current
  label observes an entity with label `l`, its current label is increased to the
  **least upper bound** of the two labels"* — taint accumulation by join, bounded
  by the top label. This is exactly `store.label' := store.label ⊔ cmd.label`.
  <https://hackage.haskell.org/package/lio-0.9.2.2/docs/LIO-Core.html> ,
  <https://hackage.haskell.org/package/lio> ,
  <https://github.com/PLSysSec/lio>
- **Buiras–Vytiniotis–Russo, _On Dynamic Flow-Sensitive Floating-Label Systems_
  (CSF 2015)** — the floating-label current-label discipline and its
  flow-sensitivity, with the noninterference proof. The reference for "a single
  label that floats and its soundness." <https://arxiv.org/pdf/1507.06189>
- **Vassena–Russo et al., _From Fine- to Coarse-Grained Dynamic Information Flow
  Control and Back_ (POPL 2019 / tutorial)** — the equivalence of per-value
  (fine-grained) vs. single-current-label (coarse-grained) IFC; warrant for
  choosing the *single joined label* over per-cell labels when the parallel
  guarantee is the same. <https://arxiv.org/pdf/2208.13560>
- **Rajani–Garg, _Types for Information Flow Control: Labeling Granularity and
  Semantic Models_ (CSF 2018)** — the granularity spectrum (per-reference vs.
  floating) and the logical-relations semantic model for each; the closest
  match to a *typed* (LRel) treatment of store labels.
  <https://people.mpi-sws.org/~dg/papers/csf2018.pdf>

**Store-cell labels through a fold, verified.**
- **Vassena–Russo–Buiras–Waye, _MAC: A verified static information-flow control
  library_ (JLAMP 2018)** — a mechanized IFC library where labelled mutable
  references carry a label and updates respect the lattice flow; the closest
  *verified* per-reference-label prior art. <https://www.sciencedirect.com/science/article/pii/S235222081730069X>
- **Parker–Vazou–Hicks, _LWeb_ (POPL 2019)** — label-tracking through stateful
  (database) operations with a machine-checked noninterference core.
  <https://arxiv.org/pdf/1901.07665>
- **Cecchetti–Myers–Arden, _Nonmalleable Information Flow Control_ (CCS 2017)** —
  the integrity/robust-declassification discipline that governs *when* a label
  may move down (the boundary the ⊔-only join stays strictly inside).
  <https://arxiv.org/pdf/1708.08596>
- **Zheng–Myers, _Dynamic Security Labels and Static Information Flow Control_**
  — Jif's run-time labels: a label carried as data through execution and joined,
  the DLM analogue of a store-carried label.
  <https://www.cs.purdue.edu/homes/xyzhang/fall07/Papers/myers1.pdf>
- **Bell–LaPadula** — *once high data enters, every subsequent output is tainted
  at the elevated level*: taint elevates monotonically, never declassifies. The
  ⊔-only join IS this discipline. (Reused from inc3 §0.)
  <https://www.sciencedirect.com/topics/computer-science/lapadula-model>

**Convergence of a joined label = the CRDT / CALM join-semilattice argument.**
- **Shapiro–Preguiça–Baquero–Zawirski, CRDTs** — state-based CRDTs converge iff
  replica states form a **join-semilattice**, updates are **monotone** (inflation),
  and merge computes the **least upper bound**; commutativity ⇒ reorder-tolerance,
  idempotence ⇒ duplicate-tolerance, associativity ⇒ batching. The store label
  under ⊔ is *exactly* a grow-only (G-set-shaped) CRDT. (Delta-state variant:
  <https://arxiv.org/pdf/1603.01529>.)
- **Gomes–Kleppmann–Mulligan–Beresford, _Verifying Strong Eventual Consistency_
  (OOPSLA 2017, Isabelle/HOL)** — the *abstract convergence theorem* over order
  relations; the mechanized core `DLCD.Calm.merge_le_iff` already instantiates.
  <https://martin.kleppmann.com/papers/crdt-isabelle-oopsla17.pdf>
- **Hellerstein–Alvaro, CALM (CACM 2020 / arXiv:1901.01930)** — monotone ⇒
  coordination-free; the store label, being monotone-join, is the coordination-free
  component of a `(register, label)` product. <https://arxiv.org/pdf/1901.01930>

**The lens these give us.** The store label is a **floating label** (LIO) whose
convergence is the **join-semilattice CRDT** argument (Shapiro / Gomes) and whose
soundness is **Bell–LaPadula monotone taint**. All three are already partially
in-tree: `DLCD.Calm` is the join-semilattice machinery; `DLCD.LabelFlow` is a
*per-cell* (fine-grained, option b) floating-store already proven noninterferent;
`DLC.Label.join` is the ⊔. Closing the fence is **assembling proven parts**, not
inventing an algebra.

---

## 1. The fence, precisely — and what is ALREADY tracked

### 1.1 Two store models already coexist in DLC-D

| layer | module | store | label tracking | status |
|---|---|---|---|---|
| **semantic / operational NI** | `DLCD.LabelFlow` (2.b) | `LStore := Label → Term` (**per-cell**, option b) | **YES** — each write goes to cell `lc.label`, no-write-down; `log_noninterference` is the Goguen–Meseguer purge | `DLCD_log_noninterference` **proven** |
| **typed / LRel NI** | `DLCD.DistributedNI` (2.d) + `TypedLog` (2.h) | bare `Term` at a **fixed** `φ` / `at χ ℓ` | **NO** — `WellTypedCmd φ` assumes each command is a `φ ⊸ φ` **endomorphism**; `LowEquivG` is at a *fixed* store type | `DLCD_distributed_noninterference`, `DLCD_wellTypedLog_implies_htyped` **proven** *with the fence* |
| **register substrate** | `DLCD.Rsm`, `Consensus`, `Linearizable` | bare `Term` | **NO** — `applyCommand c s = reduceWithFuel (app c.payload s)`; store carries no label | `DLCD_single_linearization`, `…converge…` **proven** *with the fence* |

**So the fence is specifically about the TYPED substrate** (`Rsm`/`DistributedNI`/
`Linearizable`/`TypedLog`), where the committed store is a fixed `Term` whose IFC
classification is an **assumption** (`WellTypedCmd φ`'s fixed φ), not a value
computed by the fold. `LabelFlow` already closes the *semantic* half with per-cell
labels — that is important context: **per-cell tracking (option b) is proven to
preserve NI in this very codebase**, so the design question is not "does label
tracking work" (it does) but "what is the cheapest model that closes the *typed*
fence without disturbing the proven typed guarantees."

### 1.2 The risk inc4 flagged (validated)

inc3 gave `runCmd (command M c ℓ) s ▷ liftLabel ℓ (app M s) : φ@ℓ` — running a
command **taints the result at ℓ**. inc4 §4.3 found: routing `runCmd` into the
operational fold makes the store type **accrete without bound** —
`runCmd V s : φ@ℓ` *consumes* `s:φ` but *produces* `φ@ℓ`, so slot `n+1`'s `runCmd`
demands `s:φ` and gets `s:φ@ℓ₀`; the modality **nests**: `φ @ ℓ₀ @ ℓ₁ @ …`.
`TypedLog.WellTypedCmd φ` and the whole `DistributedNI` store-typing chain assume
the store **stays at φ** across the fold, so the naive nested accretion **breaks**
the typed guarantees. The current code keeps `runCmd` **out** of the loop
(`applyCommand = app payload store`, store stays bare `Term`) precisely to avoid
this. **The hazard is TYPE-level (the nesting `at @ … @ …`), not value-level;
inc4 §4.1 confirmed value-level convergence survives any store representation.**

---

## 2. The store-label model — RECOMMEND (a): a single floating label joined by ⊔

Three options were weighed against LIO (§0), against `LabelFlow`'s existing per-cell
model, and against the accretion hazard (§1.2):

| | model | store | bound on label | accretion hazard | cost |
|---|---|---|---|---|---|
| **(a) RECOMMENDED** | single **floating** label joined by ⊔ (LIO) | `(Term, Label)`; `label' = label ⊔ ℓc` | **bounded** — `≤ ℓ₀ ⊔ (⊔ all ℓc) ≤ ⊤`, idempotent, no nesting | **eliminated** — one `at φ (⊔ℓ)`, never `@…@…` | **S** (parallel monotone fold) |
| (b) per-cell labels | `LStore := Label → Term` | already in `LabelFlow` | n/a (indexed by label) | n/a | already paid at semantic layer; **heavy** to lift to the typed LRel layer |
| (c) type-level index on the whole store | `Replicated φ ℓ` for the store | type index | bounded if index joins | needs `Replicated`-elimination in the loop (inc3 `runCmd`) → §1.2 hazard unless the index *joins* not *nests* | **M–L**; ties to the `runCmd`-in-loop churn |

**Recommendation: (a).** It is the unique model that (i) is **bounded and
idempotent** by construction (⊔ into a *single* label — `ℓ ⊔ ℓ = ℓ`, so a repeated
command's label adds nothing; the join of all applied labels is `≤ ⊤` regardless
of multiplicity), directly killing the unbounded-`@…@…` accretion inc4 flagged;
(ii) is the **LIO floating-label** discipline with a machine-checked NI pedigree
(§0); (iii) decomposes the store as a **product** `(register-needing-consensus,
G-set-CRDT-label)` whose label component plugs *directly* into the already-proven
`DLCD.Calm` join-semilattice machinery (§3); and (iv) leaves the **Term-level fold
byte-identical** — the label is tracked as a *parallel* deterministic fold, so
every existing Term proof is untouched (§4).

Option (b) is heavier at the typed layer and is *already* discharged at the
semantic layer (`LabelFlow`), so re-doing it in LRel buys little. Option (c) drags
in the `runCmd`-in-loop churn (inc3/inc4) and is only sound if the index *joins*
(reducing to (a)'s algebra anyway) rather than *nests* (the hazard).

**The model, concretely (proposed, standalone; see §5 for placement):**

```lean
-- the label a single command taints at (inc4 Open Q4: sourced from the
-- first-class `Term.command M c ℓ`'s label, or an added Rsm.Command field).
def labelOf (c : Command) : Label := …          -- ⊥ for an unguarded skeleton write

-- THE FLOATING STORE LABEL: fold ⊔ over the applied prefix (parallel to
-- applyPrefix's Term fold; ORDER-SENSITIVE foldl, but ⊔ makes it order-INSENSITIVE
-- too — see §3).
def storeLabel (ℓ₀ : Label) (cmds : CommittedLog) : Label :=
  cmds.foldl (fun ℓ c => Label.join ℓ (labelOf c)) ℓ₀
```

The **typed store type** is then `φ @ (storeLabel ℓ₀ prefix)` — a *single* `at`
with the *joined* label, **never a nest**. "The committed store's IFC
classification after applying prefix `P`" becomes the **computed value**
`storeLabel ℓ₀ P`, closing the fence: the classification is *tracked through the
fold* as a theorem, not assumed fixed.

---

## 3. Convergence preservation — the load-bearing check (VERDICT: PRESERVED, additive)

This is the crux the mandate names. Two independent reasons the labeled store keeps
`replicas_converge_on_prefix` / `replicas_converge_via_consensus` /
`single_linearization` provable:

### 3.1 SMR convergence here is order-SENSITIVE, so ANY deterministic accumulator survives

`replicas_converge_on_prefix` (Rsm) is proved by `rw [h1, h2, hlen]`: the store is
a **function of the applied prefix**, and the theorem **never inspects the store
value**. Its content is *"same prefix (same length, same log, same init) ⇒ same
store."* A parallel label fold `storeLabel ℓ₀ (log.take k)` is *also* a
deterministic function of the prefix, so the pair `(applyPrefix init P,
storeLabel ℓ₀ P)` is a function of `P` — the identical `rw` closes convergence on
the pair. **[RE-FOUND], mechanical** (byte-identical if the label is tracked as a
*separate* function rather than fused into `Replica.store`; see §5). The same holds
for `replicas_converge_via_consensus` and `single_linearization`, which rest on the
same determinism, not on the store value (inc4 §4.1 established this
representation-independence via Reynolds/data-refinement).

**This is the decisive point: convergence does NOT even need ⊔'s
commutativity/associativity/idempotence** — because the fold is over a *committed
total order* (same prefix = same order). ⊔'s laws are a *bonus* (§3.2), not a
requirement. So closing the fence via a joined label **cannot** break convergence.

### 3.2 The join laws make the label a CALM/CRDT component — convergence for FREE, coordination-free

Because ⊔ *is* commutative + associative + idempotent (`Label.join` = componentwise
`levelMax` on a 3-chain; `Label.join_assoc`/`join_bottom_*` already in
`IndexedMonad.lean`, and `join_comm`/`join_idem` are one-line `cases <;> decide`
per component, cf. `GradedBridge.join_idem`), the label component satisfies the
*stronger* CALM property: it converges **regardless of delivery order or
duplication**, with **no coordination** — it is a grow-only (G-set-shaped) CRDT.

Concretely, `Label` is a `SemilatticeSup` (3 cheap laws), so the label fold IS an
instance of `DLCD.Calm.merge` (`merge ds s = ds.foldl (· ⊔ ·) s`), and
`Calm.coordination_free_convergence` applies **verbatim**: two replicas that
absorbed the **same set** of command labels reach the **same** store label, no
quorum/agreement/order. So the store decomposes as a **product**:

```
store = ( Term register  ,  Label floating-label )
          ↑ order-SENSITIVE   ↑ order-INSENSITIVE (CALM)
          needs consensus     converges coordination-free
```

### 3.3 CALM interaction (mandate point 3): the label-join composes as a PRODUCT lattice

`Calm` already proves coordination-free convergence over any `[SemilatticeSup L]`.
The `(Term-under-consensus, Label-under-⊔)` store is a **product**: the label
factor is a `SemilatticeSup` and plugs into `Calm.merge`/`coordination_free_
convergence` directly; the register factor keeps its consensus route
(`Consensus.replicas_converge_via_consensus`). If one wanted a *fully* CALM store
(both factors monotone — e.g. a grow-only register), the product of two
`SemilatticeSup`s is a `SemilatticeSup` (componentwise ⊔), and
`coordination_free_convergence` lifts to the product with no new proof (Mathlib's
`Prod.instSemilatticeSup`). **So the label-join composes with CALM as a product
lattice — additive, no re-proof.** This is a clean new corollary, not a hazard.

**Convergence-preservation verdict: PRESERVED, and strengthened.** Closing the
fence keeps convergence provable — trivially at the value level (order-sensitive
determinism), and with a coordination-free bonus at the label level (CALM product).
**No convergence theorem is re-proved from scratch.**

---

## 4. TypedLog / DistributedNI re-founding — does the fence close as a THEOREM?

### 4.1 The label is PUBLIC — the reason NI re-founds without re-proof

The pivotal observation: `storeLabel ℓ₀ P` is a **deterministic function of the
committed log `P`**, which is **public protocol data** shared byte-identically by
both runs of any two-run NI argument (`LowEquivG` fixes `g₁.log = g₂.log`). The
label therefore **carries no secret store content** and is **identical in both
runs**. A label that is public and equal in both runs can *never* be a leak
channel. This is why the join model is guarantee-preserving: it adds a public,
run-agnostic index, not a secret-dependent one.

### 4.2 Per-guarantee re-founding ledger

| guarantee | under join-label model | flag |
|---|---|---|
| `worldStep_preserves_high` (`DistributedNI`) | **unchanged**. The high gate fires at `at χ ℓhigh` with `ℓhigh ⋠ ℓLow`. Under ⊔, the label only **rises** (`ℓ ≤ ℓ ⊔ ℓc`); if `ℓhigh ⋠ ℓLow` then `ℓhigh ⊔ ℓc ⋠ ℓLow` (join ≥ ℓhigh, and `le` is monotone) — **high stays high**. Taint monotone (Bell–LaPadula). The gate is preserved and *strengthened* (never declassifies). | **[RE-FOUND]** + new monotonicity lemma `high_stays_high` |
| `applyCommand_preserves_LRel` (the load-bearing low step) | **byte-identical**. It is about the **Term** endomorphism (`φ ⊸ φ` via `fundamental`/`lrel_self`); the label component doesn't touch it. | **byte-identical** |
| `distributed_noninterference` (capstone) | high case byte-identical; NEW content is the label-evolution lemma (`storeLabel` folds to the join) + optional restatement at `φ @ (storeLabel …)`. Core NI proof untouched. | **[RE-FOUND]**, additive |
| `wellTypedLog_implies_htyped` / `WellTypedCmd` (`TypedLog`) | **byte-identical as-is**; the endomorphism `φ ⊸ φ` still preserves the *underlying* `φ`. The join model **adds** a tracked label index on top — `WellTypedCmd` becomes `φ @ ℓ ⊸ φ @ (ℓ ⊔ ℓc)` (the payload preserves `φ`; the label index accretes by ⊔). This is the **theorem** replacing the fixed-`φ` assumption. | **[RE-FOUND]** (fixed-φ assumption → computed ⊔-index) |
| `single_linearization` (`Linearizable`) | trajectory `σ` returns `(Term, Label)` pairs; proof is the same (`h1, h2`). | **[RE-FOUND]**, mechanical (byte-identical if label tracked separately) |
| `log_noninterference` (`LabelFlow`, per-cell) | **untouched** — different (semantic) layer; the join model is the *typed* analogue, complementary. | **byte-identical** |
| `replicas_converge_*`, `coordination_free_convergence` | §3 — preserved; label is a CALM product factor. | **[RE-FOUND]** / byte-identical |

### 4.3 Does the fence close as a THEOREM? YES — with an honest caveat on what it buys

**Closed as a theorem:** with the store labeled by `storeLabel ℓ₀ P = ⊔` of the
applied labels, "the store's classification is tracked through the fold" is the
*computed* lemma `storeLabel ℓ₀ (P ++ [c]) = storeLabel ℓ₀ P ⊔ labelOf c` +
monotonicity + boundedness — no longer the fixed-`φ` **assumption**
`WellTypedCmd φ`. The `at χ ℓ`-typed store type is now `at φ (storeLabel ℓ₀ P)`,
a value the fold produces. **The disclosed fence is closed.**

**Honest caveat (the "buys what" question).** Because the label is *public* (§4.1),
this does **not strengthen the confidentiality theorem** in any observable way —
`worldStep_preserves_high` already holds for *arbitrary* store evolution at a fixed
high type, so making the label explicit does not block a leak that was previously
possible. What it buys is **modelling completeness**: per-write taint accretion
(low store + high write ⇒ store reclassified high) is now *modeled and proven
sound* (the reclassification only ever **hides more** from a fixed observer — the
low-view can only shrink monotonically, which is exactly `LabelFlow`'s
no-write-down projected to the single-label setting). It converts an *assumption*
(store stays at φ) into a *tracked invariant*, and it makes the typed layer
faithful to the per-cell semantic layer. That is a real, but **polish-grade**,
improvement — not a correctness fix.

### 4.4 Does closing the fence force re-proving NI/linearizability from scratch? — NO

**Verdict: NO re-proof from scratch.** The Term-level proofs that carry all the
real NI/convergence/linearizability content (`applyCommand_preserves_LRel` via
`fundamental`; the `rw`-based convergence; `store_is_seq_prefix`) are **untouched**
because the join model tracks the label as a *parallel* fold and leaves the Term
fold byte-identical. The new material is **additive**: a label-evolution lemma,
`high_stays_high` monotonicity, boundedness, and the CALM product corollary. This
is the guarantee-preserving path; it succeeds **precisely because** the label is
public, monotone, and factored out of the register.

---

## 4b. Can `runCmd` finally enter the operational loop? — NOT NEEDED (recommend: keep it out)

The join model **decouples** the label from `runCmd`. inc4 §4.4's route to putting
`runCmd` in the loop needs a `stripLabel₁` peel of the `liftLabel ℓ` cap to keep
the Term byte-identical — and even then the *nesting* hazard (§1.2) lurks if the
peel is forgotten. The join model instead tracks the label as a **separate `Label`
fold** (`storeLabel`), so:

- **The Term fold stays `applyCommand = app payload store`** (byte-identical); no
  `runCmd`, no `liftLabel` cap, no peel, no nesting.
- **The label is folded by ⊔ in parallel** — a single `Label`, bounded, no `@…@…`.

So `runCmd` does **not** need to enter the loop to close the fence. If one *later*
wants the operational store value to literally carry the `liftLabel ℓ` cap (a
genuinely `at φ ℓ`-typed *term* store, option c), inc4 §4.4's peel-or-track applies
— but that is strictly more churn for no guarantee gain over the parallel-label
model. **Recommendation: keep `runCmd` out of the operational loop; track the label
separately.** This is the cheapest sound realization and matches how `LabelFlow`
already tracks labels (per-cell) without routing the Term through `runCmd`.

---

## 5. Impact map + staging + honest cost

### 5.1 The gating precondition (inc4 Open Q4): a real per-command label

`Rsm.Command` currently has `cap : Option Prop'` (a *proposition*), **no `Label`
field**. `storeLabel`'s ⊔ needs an actual lattice element `labelOf c : Label`.
Three sources, in order of preference:

1. **Track over the first-class log** `List (Term.command M c ℓ)` — the label `ℓ`
   is already a field (inc3). Cleanest, but ties to the inc4 "strip vs. keep"
   ruling on the log representation.
2. **Add `label : Label` to `Rsm.Command`** — a struct change; ripples to every
   witness and the `Command` axiom snapshot (measured against inc4: `LabelFlow`
   already carries a separate `LCommand { cmd, label }`, so the additive
   `LCommand`-style wrapper is the precedent — *do it as a wrapper, not a field*,
   to keep `Command` byte-identical).
3. **`labelOf c := ⊥`** for the skeleton (unguarded) case — makes the metatheorem
   *sound but vacuous* (all-⊥) until a real label is wired. Acceptable only as a
   scaffold; the anti-vacuity witness must use genuine non-⊥ labels via (1)/(2).

**Recommendation: reuse `LabelFlow`'s `LCommand { cmd, label }`** (already in-tree,
already governed under `DLCD_log_noninterference`) as the label source — the
metatheorem then folds ⊔ over `log.map (·.label)`, non-vacuously, with **no new
struct and no `Command` snapshot churn.**

### 5.2 The minimal first sub-increment (additive, all existing files byte-identical)

A **new file** `DLCD/StoreLabel.lean` (mirroring `Calm.lean`'s self-contained
shape), depending only on `DLCD.LabelFlow` (for `LCommand`/`Label.le` laws) and
`DLCD.Calm` (for the CRDT bridge). It proves, over `LCommand` labels:

1. `storeLabel ℓ₀ log := (log.map (·.label)).foldl Label.join ℓ₀` — the floating
   store label as a fold.
2. `storeLabel_snoc` — `storeLabel ℓ₀ (log ++ [lc]) = storeLabel ℓ₀ log ⊔ lc.label`
   (the fence-closing *evolution* lemma: classification tracked through the fold).
3. `storeLabel_bounded` — `storeLabel ℓ₀ log ≤ ℓ₀ ⊔ (join of all labels) ≤ ⊤`
   (bounded, no unbounded accretion — kills the inc4 hazard).
4. `storeLabel_monotone` / `high_stays_high` — the label only rises; a high store
   stays high under any further writes (Bell–LaPadula; feeds `worldStep_preserves_
   high` re-founding).
5. `storeLabel_idem_dup` / `storeLabel_set_invariant` — duplicate- and (via the
   ⊔ laws) order-insensitivity, routed through **`Calm.merge_mem_invariant`**
   (the label IS a `Calm` G-set) — the coordination-free convergence of the label.
6. `storeLabel_converges` — two replicas on the same prefix get the same store
   label (trivial determinism; the pair-convergence bridge to Rsm).
7. `label_calm_product` — the `(register, label)` product-lattice CALM corollary
   (§3.3), lifting `Calm.coordination_free_convergence` to the label factor.
8. Anti-vacuity `StoreLabelWitness` — a concrete high+low log (reuse
   `LabelFlowWitness`'s `[hiCmd, loCmd]`) where `storeLabel ⊥ log = hi ≠ ⊥`
   (label genuinely rose) yet convergence/monotonicity hold; a right-reason bite
   where a *meet* (declassifying) update would break monotonicity.

**All existing `DLCD/*` files stay byte-identical; all 12 governed `DLCD_*` stay
`proven`; every axiom snapshot intact.** Optionally govern a new
`DLCD_store_label_tracked` (expect `[propext]` ⊂ permitted) with its own snapshot.
`check-claims.sh` stays green (this is `spec/**` + an additive `lean/**` file that
makes no claim exceeding the ledger).

### 5.3 Later sub-increments (gated, larger — recommend DEFER)

- **5b:** fuse the tracked label into the typed layer — restate
  `worldStep_preserves_low_typed` / `WellTypedCmd` at `φ @ (storeLabel …)` and add
  a `LowEquivG`-at-tracked-label variant. Additive to `TypedLog`/`DistributedNI`;
  **[RE-FOUND]**, medium. Only worth it if a consumer needs the tracked-label NI
  statement.
- **5c:** fuse the label into `Replica`/`applyPrefix` (return `(Term, Label)`) so
  the *operational* store carries it. Ripples to convergence/linearizability
  witnesses (pair RHSs) — **[RE-PROVE], mechanical**, but touches snapshots.
  **Defer** unless the runtime store must carry the label.
- **5d (off-path):** option (c) `runCmd`-in-loop with a `liftLabel ℓ` cap on the
  Term store (inc4 §4.4 peel). Strictly more churn than 5a–5c for no guarantee
  gain. **Do not pursue** unless a `Replicated φ ℓ`-typed *term* store is required.

### 5.4 Honest cost

- **First sub-increment (5a):** **S** — ~1 additive file, ~8 theorems + witness,
  all leaning on already-proven `Calm`/`LabelFlow`/`Label.join` parts. Low risk;
  nothing existing moves. **This is a SMALL fence-closing.**
- **Full fusion (5b+5c):** **M** — additive re-foundings, mechanical re-proofs of
  value witnesses, some snapshot churn. Medium risk, contained.
- **It does NOT ripple into a large re-proof.** The fence closes *additively*
  because the label is public/monotone/factored. The one genuine dependency is the
  per-command-label source (§5.1), solved by reusing `LCommand`.

---

## 6. DO-NOW vs DEFER — the honest recommendation

**Recommendation: DO the minimal sub-increment 5a now; DEFER 5b–5d.**

**Why do 5a now:**
- It is **cheap and additive** (§5.4, **S**), leaning entirely on already-proven
  in-tree machinery (`Calm`, `LabelFlow`, `Label.join`).
- It **definitively answers** the fence's hard questions — convergence survives
  (§3), NI re-founds without scratch re-proof (§4), the label is bounded (no
  accretion), and it composes with CALM as a product (§3.3). These answers are
  valuable *even if* the fusion is deferred, because they retire the *risk* the
  fence documented.
- It closes the disclosed fence *as a theorem* (`storeLabel` evolution +
  boundedness + monotonicity), which is a genuine ledger improvement.
- It is **non-vacuous** (the label genuinely rises; reuse `LabelFlowWitness`).

**Why defer 5b–5d:**
- The honest caveat (§4.3): the tracked label is **public**, so fusing it into the
  typed NI statement (5b) or the operational store (5c) **does not strengthen any
  security guarantee** — it is faithfulness/completeness polish. The fixed-`φ`
  assumption is not *unsound*; it is *incomplete* (doesn't model reclassification).
- 5c/5d touch snapshots and witnesses for no guarantee gain over the standalone
  metatheorem. The cost/value ratio inverts past 5a.

**The genuine "should we" answer:** closing this fence is **worth a small
increment, not a large one.** The join-label model is the right design and is
provably guarantee-preserving; but because the accreted label carries no secret,
the payoff is modelling completeness, so the *investment should match* — do the
cheap standalone metatheorem that retires the risk and closes the fence as a
theorem, and stop there unless a downstream consumer (e.g. a runtime that surfaces
the store's current clearance) needs the label fused into the operational store.

---

## 7. Open questions for ruling

1. **Do 5a now?** Recommend **yes** — cheap, additive, closes the fence as a
   theorem, retires the accretion risk, non-vacuous. Confirm.
2. **Label source (inc4 Open Q4).** Recommend **reuse `LabelFlow.LCommand
   { cmd, label }`** as `labelOf` — already in-tree, already governed, no
   `Command` struct/snapshot churn. Or do we want a real `label : Label` on
   `Rsm.Command` (struct change) / to track over the first-class `command M c ℓ`
   log (ties to inc4 strip-vs-keep)?
3. **Defer 5b–5d?** Recommend **defer** — the public label means fusion is
   completeness polish, not a security gain. Confirm we stop at 5a unless a
   consumer needs the fused store.
4. **Govern a new `DLCD_store_label_tracked`?** A 13th governed `DLCD_*` entry
   (own axiom snapshot, expect `[propext]`), or fold the re-founding note into the
   existing `DLCD_single_linearization` / `DLCD_distributed_noninterference`
   `open` items (which currently *name* this fence)?
5. **Monotone-hiding as the security content.** The one *provable* soundness fact
   is that reclassification only ever **shrinks the low view** (join rises ⇒ more
   cells hidden), the single-label projection of `LabelFlow`'s no-write-down.
   Should 5a state this as its headline (a genuine, if weak, NI-flavoured lemma),
   or leave it as a note and keep 5a purely algebraic (evolution + bound +
   convergence)?

---

## 8. Gate check

- **REALIZABLE + guarantee-preserving.** §3–§4 establish that closing the fence via
  the ⊔-join floating label is **additive**: convergence is preserved (order-
  sensitive determinism, §3.1; CALM bonus, §3.2–3.3), NI/linearizability
  **re-found without scratch re-proof** (§4.4) because the label is public,
  monotone, and factored out of the register. No guarantee is weakened; the fixed-`φ`
  **assumption** becomes a **computed ⊔-index theorem**.
- **Honest cost.** §4.3 states plainly that the tracked label is *public* and so
  the payoff is **modelling completeness, not a stronger confidentiality theorem**.
  §5.4 sizes it: **S** for the standalone metatheorem, **M** for full fusion, no
  large re-proof. §5.1 names the one real precondition (per-command label source).
- **Cheapest guarantee-preserving path.** Sub-increment 5a: a single additive
  `DLCD/StoreLabel.lean` reusing `Calm`/`LabelFlow`/`Label.join`, all existing
  files byte-identical, all governed `DLCD_*` `proven`, `check-claims.sh` green.
- **Honest do-now-vs-defer.** §6: **do 5a; defer 5b–5d.** A small fence-closing,
  matched to a polish-grade (not correctness) payoff.
