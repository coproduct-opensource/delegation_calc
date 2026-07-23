# R1-inc4 — Re-founding the DLCD distributed guarantees onto `Term.command`

**Status:** PROPOSAL (design only; no `.lean`/`.rs` edits). Gated on review.
**Branch:** `dlc-d/phase0-carve` (HEAD `305e48b`).
**Scope:** re-express the DLC-D distributed layer so that authorization comes
from the **first-classed, `commit-I`-typed** `Term.command` (inc2/inc3) rather
than the operational-model wrapper `Rsm.Command` + the audited `Authorized`
side-condition — while keeping all **11 governed `DLCD_*` guarantees `proven`**.

---

## 0. Prior art (web-searched 2026-07-23; URLs recorded)

The two design moves here — (i) internalizing an operational-model wrapper into
a **typed term** and recovering a safety property by **inversion on typing**,
and (ii) changing the underlying representation while **preserving a proven
guarantee suite** — are both standard, named techniques.

**Capability/safety by typing inversion (canonical-forms / generation lemma).**
Type-safety is proved by *progress* (via **canonical-forms** lemmas: a value at
type `T` has the shape `T`'s introduction form dictates) and *preservation* (via
**inversion / generation** lemmas: a typing derivation for a term of a given
head shape can only have come from that head's rule). Re-expressing
"the committed write was authorized" as an inversion on `commit-I` is exactly a
generation lemma: `command M c ℓ` has a *unique* typing rule, so a derivation of
its type *inverts* to the `says`-credential premise.

- TAPL §13.5 *Safety* (progress via canonical forms; preservation via inversion):
  https://flylib.com/books/en/4.279.1.82/1/
- Grossman, *CS152 Lecture 10 — Type-Safety Proof* (progress+preservation, the
  inversion/canonical-forms split): https://homes.cs.washington.edu/~djg/2011sp/lec10.pdf
- Twelf, *Canonical forms lemma*: http://twelf.org/wiki/Canonical_forms_lemma
- *Type-Directed Operational Semantics for Gradual Typing* (ECOOP 2021) —
  making type annotations operationally load-bearing by internalizing them into
  the term (the same "the wrapper becomes a typed term" move `command M c ℓ`
  makes): https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2021.12

**Guarantee-preserving representation change (refinement / representation
independence / parametricity).** A refactor that changes the *representation*
under a proof suite is guarantee-preserving iff the guarantees are stated over
the abstract behaviour, not the concrete rep — Reynolds' abstraction theorem /
parametricity ("all computations give the same results under different
implementations of an abstract type") and data-refinement ("properties proven of
the abstract spec are preserved by the concrete implementation, by construction,
without re-proof").

- Reynolds, *Types, Abstraction and Parametric Polymorphism*:
  https://people.mpi-sws.org/~dreyer/tor/papers/reynolds.pdf
- Wadler, *Theorems for Free!*: https://www2.cs.sfu.ca/CourseCentral/831/burton/Notes/July14/free.pdf
- Mitchell, *Representation Independence and Data Abstraction* (POPL):
  https://dl.acm.org/doi/10.1145/512644.512669
- Banerjee–Naumann, *Ownership Confinement Ensures Representation Independence
  for OO Programs*: https://arxiv.org/pdf/cs/0212003
- *Generalized Security-Preserving Refinement for Concurrent Systems* (2025):
  https://arxiv.org/pdf/2511.06862
- MIT 6.005, *Abstraction Functions & Rep Invariants*:
  https://ocw.mit.edu/ans7870/6/6.005/s16/classes/13-abstraction-functions-rep-invariants/
- Hawblitzel et al., *IronFleet* (a real RSM whose safety+liveness suite is
  preserved across module refactors — the status-manifest discipline `Summary`
  already mirrors):
  https://www.microsoft.com/en-us/research/publication/ironfleet-proving-safety-liveness-practical-distributed-systems/

**The lens these give us.** Nine of the eleven DLCD guarantees are stated over
the *abstract behaviour* "the store is a deterministic function of the applied
prefix" and over a *type-parametric* quorum (`Votes n V`). By Reynolds/refinement
they are **insensitive to the log-entry representation** — so a representation
change buys them nothing and risks re-proof. Only `capability_safety` is *about*
the entry's internal structure; only it benefits from the typing-native
foundation. That asymmetry drives the recommendation below.

---

## 1. What is first-classed (inc1–3) vs. what DLCD still uses

| Layer | inc2/inc3 first-class calculus | DLCD operational wrapper |
|---|---|---|
| entry | `Term.command M c ℓ` (`M` payload term, `c` **credential term**, `ℓ` `Label`) | `Rsm.Command { payload : Term, cap : Option Prop' }` (no label) |
| type | `commit-I`: `Γ⊢c:issuer says cap`, `Γ⊢M:φ⊃φ` ⊢ `command M c ℓ : Replicated (φ⊃φ) ℓ` | none (operational, untyped store) |
| run | `runCmd`: `runCmd V s : φ @ ℓ`, `runCmd (command M c ℓ) s ▷ liftLabel ℓ (app M s)` | `applyCommand c s = reduceWithFuel (app c.payload s)` |
| authz | **inversion on `commit-I`** (recovers the `says`-credential premise) | `Authorized c issuer := ∃ Γ capTerm capProp, c.cap = some (issuer says capProp) ∧ Nonempty (Deriv Γ capTerm (issuer says capProp))` — an audit using the **additive** `Deriv`, not `commit-I` |

The two calculus objects are **not 1-1**: `Rsm.Command.cap : Option Prop'` is a
*proposition* (`issuer says capProp`); `Term.command`'s `c : Term` is a *proof
term* (a credential) of that proposition; and `Term.command` additionally carries
a `Label ℓ` the wrapper has no field for.

---

## 2. The `Rsm.Command ↔ Term.command` mapping (a **relation**, not a bijection)

Because `cap` is a proposition and `c` is a proof term, and because `ℓ` is absent
from the wrapper, neither direction is a total function:

- **wrapper → term** needs to *synthesize* (a) a credential term `c` witnessing
  `cap = some (issuer says capProp)`, and (b) a label `ℓ`. The credential term is
  *exactly* the `Nonempty (Deriv Γ capTerm (issuer says capProp))` witness that
  `Authorized` already asserts exists; `ℓ` must be supplied (see Open Q4).
- **term → wrapper** must *erase* the credential term to its proposition
  (`c : issuer says capProp` ↦ `cap := some (issuer says capProp)`) and *drop*
  the label. Erasing a term to "its type" is not a term-level function — the type
  is recovered from the derivation, not the syntax.

So the faithful bridge is a **realization relation** (a refinement/abstraction
relation, §0), not a coercion:

```lean
-- proposed (inc4, additive; NO struct change)
def CommandRealizes
    (rc : Rsm.Command) (M c : Term) (ℓ : Label)
    (Γ : Ctx) (issuer capProp φ : Prop') : Prop :=
  rc.payload = M ∧
  rc.cap = some (Prop'.says issuer capProp) ∧
  Nonempty (Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ))
```

`Rsm.Command` is the **abstract log-entry representation** the quorum/convergence
machinery is proven over; `Term.command`, related by `CommandRealizes`, is its
**typed realization**. The `commit-I` premises (`dc`, `dM`) are recoverable from
the third conjunct by inversion (§3). This is the data-refinement picture: the
abstraction function forgets the credential *term* and the label; the rep
invariant is `CommandRealizes`.

### Strip (A) vs. Keep-and-bridge (B) — **recommend B**

**Option A — STRIP the wrapper.** `CommittedLog := List Term`, each entry a
`command M c ℓ` term. Ripple (measured on the tree):

- `Votes n Command` (generic `Fin n → Option V`) → `Votes n Term` in
  `Consensus`, `MultiDecree`, `MultiDecreeLiveness`, `Liveness`, `Witness`;
  and every derived alias — `SlotBallots`, `SlotSchedule`, `WeakDecided`,
  `slotVotes`, `votesW`, `ssStarved`, `wit`.
- `applyCommand : Command → Term → Term` becomes `Term → Term → Term` and must
  destructure `command M c ℓ`; `deliver`/`worldStep`/`applyPrefix`/`seqTrajectory`
  re-typed.
- `TypedLog.WellTypedCmd φ c` (reads `c.payload`) must read the `M` subterm of a
  `command` term; `commitTyped`/`WellTypedLog`/`wellTypedLog_implies_htyped`
  restated.
- `DistributedNI` `applyCommand_steps`/`applyCommand_preserves_LRel` and the
  whole `LRel` chain reproven over the new shape (`LabelFlow`: 26 `Command`
  refs; `DistributedNI`: 19).
- Every anti-vacuity witness rebuilt.
- **Plus the §3 labeled-store type hazard bites hardest here** (see below): if
  stripped entries also drive application through `runCmd`, the label accretes
  and the typed-store fold stops composing; if they *don't* (`app M s` ignoring
  `c`, `ℓ`), stripping bought nothing — the credential and label ride along
  unused, strictly worse than today's explicit `cap` slot.

Estimated effort **L–XL**, 10+ files, with a **real risk of forcing
`distributed_noninterference` and `single_linearization` to be RE-PROVED**.

**Option B — KEEP the wrapper struct; add the bridge; re-express ONLY
`CapSafety` by inversion.** The log/quorum/convergence machinery is untouched
(byte-identical). We add `CommandRealizes` and the inversion theorems (§3), and
show the audited `Authorized` **coincides** with "the command is `commit-I`-typeable."
Effort **S–M**, additive, guarantee-preserving by construction (nothing else
moves).

**RECOMMENDATION: Option B.** Ten of the eleven guarantees are stated over the
representation-independent "store = function of prefix" behaviour and a
type-parametric quorum; by §0 they gain nothing from a representation change and
would only be put at re-proof risk. Only `capability_safety` is *about* the
entry's structure, and its typing-native re-founding is fully achieved by the
inversion twin **without touching the struct**. Keep `Rsm.Command` as the
abstract log-entry rep; realize it as `Term.command` through the bridge; re-found
authorization on `commit-I`. This is precisely the representation-independence
discipline: move the *one* guarantee that benefits onto the typed foundation,
preserve the representation the others are proven over.

---

## 3. Capability-safety by **inversion** (the key deliverable)

### 3.1 The inversion (generation) lemma — `commit-I`'s only inhabitant

`Term.command _ _ _` is the subject of a **single** `Deriv` constructor
(`commitI`); every other constructor's subject has a different head
(`var`/`lam`/`sign`/`pair`/`inl`/…). So a derivation of a `command`'s type
**inverts** to the `commit-I` premises. In Lean, `cases` on the (Type-valued)
`Deriv` unifies each constructor's subject index against `Term.command M c ℓ`;
all but `commitI` fail head-unification and are discharged automatically
(`Term.noConfusion`), leaving exactly the `commitI` premises. (Eliminating a
`Type`-valued `Deriv` to prove a `Prop` goal is permitted — large elimination
into `Prop` is unrestricted.)

```lean
-- proposed (inc4, CapSafety.lean, additive)
theorem command_typing_inversion
    {Γ : Ctx} {M c : Term} {ℓ : Label} {ψ : Prop'}
    (d : Deriv Γ (Term.command M c ℓ) ψ) :
    ∃ (Γₐ : List Prop') (issuer capProp φ : Prop'),
      Γ = { additive := Γₐ, linear := [] } ∧
      ψ = Prop'.replicated (Prop'.imp φ φ) ℓ ∧
      Nonempty (Deriv { additive := Γₐ, linear := [] } c (Prop'.says issuer capProp)) ∧
      Nonempty (Deriv { additive := Γₐ, linear := [] } M (Prop'.imp φ φ)) := by
  cases d with
  | commitI Γₐ issuer capProp φ ℓ' M' c' dc dM =>
      exact ⟨Γₐ, issuer, capProp, φ, rfl, rfl, ⟨dc⟩, ⟨dM⟩⟩
  -- all other constructors: head-unification with `Term.command _ _ _` fails,
  -- auto-discharged.
```

The **credential premise `dc : c : issuer says capProp` is recovered from the
value's type** — this is capability-safety re-founded: authorization is no longer
an out-of-band audit, it is *extracted by inverting the typing of the command
itself*.

### 3.2 Capability-safety, typing-native form

```lean
-- proposed (inc4, CapSafety.lean)
theorem capability_safety_by_inversion
    {Γ : Ctx} {M c : Term} {ℓ : Label} {φ : Prop'}
    (d : Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ)) :
    ∃ (issuer capProp : Prop') (Δ : Ctx),
      Nonempty (Deriv Δ c (Prop'.says issuer capProp)) := by
  obtain ⟨Γₐ, issuer, capProp, φ', _, _, hc, _⟩ := command_typing_inversion d
  exact ⟨issuer, capProp, _, hc⟩
```

Note `issuer` is **not pinned by `commit-I`'s conclusion** (`Replicated (φ⊃φ) ℓ`
omits it) — it lives only in the credential premise — so the theorem
existentially quantifies `issuer`, matching the shape of the current
`capability_safety` (`∃ issuer, Authorized c issuer`). (Open Q5.)

### 3.3 Does the governed `capability_safety` stay identical?

**Yes — governed statement stays byte-identical; the inversion form is ADDED.**
Under Option B we do **not** disturb `Authorized`, `WellFormedLog`, or
`capability_safety` (over `WellFormedLog`). We add, as the typing-native twin:
`command_typing_inversion`, `capability_safety_by_inversion`, and a **coincidence
bridge** proving the audited predicate and the typing witness are equivalent:

```lean
-- proposed (inc4): the audit side-condition is now BACKED BY the typing witness
theorem authorized_of_command_typing
    {M c : Term} {ℓ : Label} {issuer capProp φ : Prop'} {Γ : Ctx}
    (d : Deriv Γ (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ))
    (hguard : (⟨M, some (Prop'.says issuer capProp)⟩ : Rsm.Command).cap
                = some (Prop'.says issuer capProp)) :
    Authorized ⟨M, some (Prop'.says issuer capProp)⟩ issuer
-- and the converse: an `Authorized` wrapper realizes SOME `command M c ℓ`
-- typeable by commit-I (via CommandRealizes), for a supplied ℓ.
```

So `Authorized` is no longer a *free-standing* audit: it is shown **equivalent to
`commit-I`-typeability**, i.e. the side-condition is re-founded on the typing
inversion. `capability_safety`'s statement and proof are unchanged (its axiom
snapshot `dlcd-capability_safety.txt` stays intact); the re-founding is the new
equivalence + inversion lemmas underneath it. Nothing governed is restated or
weakened.

---

## 4. `applyCommand` via `runCmd` — the **labeled-store convergence** analysis

Current: `applyCommand c s = (reduceWithFuel (app c.payload s) applyFuel).1`.
Proposed variant: `applyCommand' cmd s = (reduceWithFuel (runCmd (command M c ℓ) s) applyFuel).1`.

`runCmd`-β: `runCmd (command M c ℓ) s ▷ liftLabel ℓ (app M s)`, so the reduced
store becomes `liftLabel ℓ (nf(app M s))` — **an outer `liftLabel ℓ` now wraps the
store**. Three distinct effects, at two levels:

### 4.1 VALUE level — convergence SURVIVES (representation-independence)

`applyCommand'` is still `reduceWithFuel` of a *function* of `(cmd, s)`, hence
still a total deterministic transition; `applyPrefix'` is still a deterministic
`foldl`. Therefore:

- **`replicas_converge_on_prefix`** (Rsm) — proof is `rw [h1, h2, hlen]`: the
  store is a function of the applied prefix and the theorem **never inspects the
  store value**. **Byte-identical, [RE-FOUND].** Convergence is
  *representation-independent* (Reynolds/refinement, §0): the extra `liftLabel ℓ`
  is invisible to a guarantee stated over "same prefix ⇒ same store."
- **`replicas_converge_via_consensus`** (Consensus), **`single_linearization`**
  (Linearizable) — rest on the same determinism, not on the store value.
  **[RE-FOUND], proofs unchanged.**
- **`Calm.coordination_free_convergence`** — uses the lattice join
  `applyδ δ s = s ⊔ δ`, **not `applyCommand` at all**. **Byte-identical,
  entirely unaffected.**

**Answer to the seed question:** yes, `worldStep`/convergence still hold with a
`liftLabel`-wrapped store — because the convergence metatheorem is about the
*fold being a function*, not about the store's shape. The label does **not** need
to be projected away *for convergence*.

### 4.2 VALUE level — concrete witnesses need RHS updates ([RE-PROVE], mechanical)

The anti-vacuity witnesses **pin the store value by `rfl`**, and those RHSs
change from `t` to `liftLabel ℓ t`:

- `Rsm.RsmAntiVacuity`: `applyCommand dup init = pair (var 0) (var 0)`;
  `converged_store_changed`.
- `Witness`: `converged_store : r1.store = pair (var 0) (var 0) := rfl`;
  `state_changed`; the `seqTrajectory` linearization equalities.
- `Linearizable` bite (`bad_off_trajectory`).

Each becomes `liftLabel ℓ (pair (var 0) (var 0))` etc. **[RE-PROVE], mechanical**
(~6–10 value equalities); still non-vacuous (`liftLabel`-headed ≠ `init`, distinct
head constructor). **Only relevant if we adopt the `runCmd` application variant**
— under the recommended first sub-increment (§5) these stay byte-identical.

### 4.3 TYPE level — the real hazard: **label accretion breaks the typed fold**

`runCmd V s : φ @ ℓ` **consumes** `s : φ` but **produces** `φ @ ℓ`. Folding
`runCmd` over a log therefore does **not** compose in a single store type: after
slot 0 the store is typed `φ @ ℓ₀`; slot 1's `runCmd` demands a store `: φ`, but
it now has `: φ @ ℓ₀`. **The label accretes** (`φ @ ℓ₀ @ ℓ₁ @ …`). `TypedLog`'s
`WellTypedCmd φ c := (payload : φ ⊃ φ) ∧ CoreTerm payload` and the entire
`DistributedNI` store-typing chain assume **the store stays at `φ` across the
fold**. So a naive `runCmd`-based `applyCommand` would force `TypedLog` +
`DistributedNI` to either

- (a) **track the growing label** — the store type changes per command (exactly
  the "Store-type change" OPEN fence already documented in `Summary`), a larger
  increment; or
- (b) **project the label away** between commands.

**This is THE key re-founding risk, and it is a TYPE-level, not a value-level,
problem.** Convergence (value-level) is safe; the *typed*-store invariant is what
`liftLabel ℓ` threatens.

### 4.4 The clean fix — label projection makes it byte-identical

At the value level, `runCmd (command M c ℓ) s ▷* liftLabel ℓ (nf(app M s))`, and
`nf(app M s)` is *exactly* the current `applyCommand`. So with a one-line peel

```lean
def stripLabel₁ : Term → Term
  | Term.liftLabel _ t => t
  | t => t

-- proposed (later sub-increment, IF we want runCmd in the loop)
def applyCommand_runCmd (M c : Term) (ℓ : Label) (s : Term) : Term :=
  stripLabel₁ (reduceWithFuel (Term.runCmd (Term.command M c ℓ) s) applyFuel).1
```

`applyCommand_runCmd M c ℓ s` is **definitionally equal to the current
`applyCommand ⟨M,_⟩ s`** (the peel cancels the single `liftLabel ℓ`), so *every*
convergence / linearizability / NI / witness proof stays **byte-identical** and
the store stays at `φ`. This is the guarantee-preserving way to put `runCmd` in
the application loop *if* we want it. **Recommendation:** do **not** put `runCmd`
in the operational loop in the first sub-increment at all — the operational store
is deliberately untyped (`Term`), and `applyCommand = app payload store` is left
exactly as-is; `runCmd` is connected only at the *typed* layer where `ℓ` is
meaningful (§5, Open Q2).

---

## 5. Impact map (Option B; minimal first sub-increment)

### Files that CHANGE (all **additive**)

| File | Change | Kind | Effort |
|---|---|---|---|
| `DLCD/CapSafety.lean` | add `command_typing_inversion`, `capability_safety_by_inversion`, `authorized_of_command_typing` + converse, `CommandRealizes`, a `commit-I` anti-vacuity witness (reuse `saysWitness` as the credential term). **Keep `Authorized`/`WellFormedLog`/`capability_safety` byte-identical.** | [RE-FOUND] additive | M (the inversion `cases` is the only real labor) |
| `lean/theorem-status.json` | note the inversion re-founding on `DLCD_capability_safety.proven_content`; optionally add governed entry `DLCD_capability_safety_by_inversion` | additive | S |
| `DLCD/Summary.lean` | optionally re-export `capability_safety_by_inversion` under the name-drift tripwire (1 `abbrev`) | additive | S |
| `lean/expected-axioms/` | `dlcd-capability_safety.txt` **UNCHANGED**; NEW `dlcd-capability_safety_by_inversion.txt` (expect `[propext]`, ⊂ the permitted set) iff governed | additive | S |

### Files BYTE-IDENTICAL (no change in first sub-increment)

`Rsm.lean`, `Consensus.lean`, `MultiDecree.lean`, `MultiDecreeLiveness.lean`,
`Liveness.lean`, `Termination.lean`, `Linearizable.lean`, `Calm.lean`,
`DistributedNI.lean`, `LabelFlow.lean`, `TypedLog.lean`, `CapSafetyLinear.lean`,
`ByzantineConsensus.lean`, `Witness.lean` — because `Command` and `applyCommand`
are unchanged. **All 11 governed `DLCD_*` stay `proven`; witnesses + snapshots
intact.**

### Per-guarantee ledger

| Guarantee | Under first sub-increment | If `runCmd`-application later adopted |
|---|---|---|
| `capability_safety` | byte-identical + inversion twin added — [RE-FOUND] | unchanged |
| `capability_safety_linear` | byte-identical | unchanged |
| `byz_agreement` | byte-identical | unchanged |
| `log_noninterference` | byte-identical | value witnesses gain `liftLabel` — [RE-PROVE] mechanical (avoided by §4.4 peel) |
| `distributed_noninterference` | byte-identical | store-type hazard §4.3 — **must** use §4.4 peel or track labels |
| `wellTypedLog_implies_htyped` | byte-identical | store-type hazard §4.3 — same |
| `single_linearization` | byte-identical | `seqTrajectory` value witnesses — [RE-PROVE] (avoided by peel) |
| `weakfair_terminates` | byte-identical | unchanged |
| `log_grows_unbounded` | byte-identical | unchanged |
| `replicas_converge_via_consensus` | byte-identical | [RE-FOUND] value-independent |
| `coordination_free_convergence` | byte-identical | unaffected (lattice store) |
| `dlc_d_slice_witness` (seal) | byte-identical | value witnesses — [RE-PROVE] (avoided by peel) |

**Nothing is forced to RE-PROVE from scratch under Option B first sub-increment.**
The only [RE-PROVE] items are the concrete value-pins, and only *if* `runCmd`
enters the application loop *without* the §4.4 label peel.

---

## 6. Migration — green-to-green sub-steps (all 11 `DLCD_*` stay `proven`)

- **4a (THIS increment, minimal):** `CapSafety.lean` — add
  `command_typing_inversion`, `capability_safety_by_inversion`, the coincidence
  bridge, `CommandRealizes`, and a `commit-I` anti-vacuity witness. Governed
  `capability_safety` unchanged. Optionally govern the new theorem + snapshot.
  **GREEN.** (This is the recommended stopping point for review.)
- **4b:** `TypedLog` — prove `WellTypedCmd φ ⟨M,_⟩` is discharged by `commit-I`'s
  `dM : M : φ⊃φ` premise via inversion (they are the *same* `φ⊃φ` obligation), so
  a `command`-typed entry *is* a well-typed command. No struct change. **GREEN.**
- **4c (gated on ruling):** promote `CommandRealizes` to a log-level relation
  `LogRealizes : CommittedLog → List Term → Prop`; prove the audited
  `WellFormedLog` and the typed `commit-I` log coincide. **GREEN.**
- **4d (optional, later):** `runCmd`-based application with the §4.4 label peel
  (`applyCommand_runCmd`), proven definitionally equal to `applyCommand` ⇒ all
  convergence/NI/witnesses byte-identical. Adopt only if `runCmd` is wanted in the
  loop; otherwise the operational layer stays on `app`. **GREEN.**
- **STRIP (Option A)** is **off** the recommended path; pursue only if a ruling
  prioritizes a single unified `List Term` log-entry type over the L–XL ripple
  and the §4.3 hazard.

---

## 7. Open questions for ruling

1. **Strip vs. keep.** Recommend **Keep + bridge (Option B)** — the 10
   representation-independent guarantees gain nothing from strip and would be put
   at re-proof risk; only `capability_safety` benefits, and fully via the
   inversion twin without a struct change. Confirm B.
2. **Labeled store.** Do we *want* the committed store's type to become `φ @ ℓ`
   per command — embracing per-write taint tracking across the log, closing the
   "store-type change" fence but forcing `TypedLog`/`DistributedNI` to track
   accreting labels (larger increment) — **or project the label away** (§4.4
   peel) to keep the store at `φ` and every witness byte-identical? Recommend
   **project-for-now**; taint-tracked store is a separate, larger increment.
3. **Governance granularity.** Should `capability_safety_by_inversion` be a NEW
   governed `DLCD_*` entry (a 12th guarantee, own axiom snapshot), or folded into
   `DLCD_capability_safety.proven_content` as the re-founding note?
4. **Where does `ℓ` come from?** `Rsm.Command` has **no label field**; the bridge
   `toTermCommand`/`CommandRealizes` needs an `ℓ`. Is it the write's IFC label
   from nucleus's `CapabilityLattice` (and if so, does `Rsm.Command` gain an `ℓ`
   field, or is `ℓ` supplied externally at realization time)?
5. **`issuer` existential.** `commit-I`'s conclusion omits `issuer`; inversion
   recovers it only from the credential premise. Confirm
   `capability_safety_by_inversion` may `∃ issuer` (matching the current
   `capability_safety`'s `∃ issuer` shape) rather than take `issuer` as input.

---

## 8. Gate check

- **REALIZABLE + guarantee-preserving.** Option B first sub-increment is purely
  additive: all 11 governed `DLCD_*` stay `proven` with witnesses + snapshots
  intact; `check-claims.sh` stays green (this is a `spec/**` doc, and it makes no
  claim exceeding the ledger — it proposes, and honestly fences the `runCmd`
  hazard).
- **Labeled-store honesty.** §4.3 states plainly that a naive `runCmd`-fold
  **breaks** the typed-store invariant by label accretion; convergence itself
  survives (value-independent), but the typed guarantees require either the §4.4
  label peel (byte-identical, recommended) or an explicit taint-tracked store
  (larger). We do **not** claim the naive `runCmd`-fold preserves the typed
  guarantees.
- **Cheapest guarantee-preserving path.** Recommended: Option B, sub-increment
  4a, `runCmd` kept **out** of the operational loop.
