# DLC-D Phase R1 — Increment 3: `command` ELIMINATION + reduction + label-tracking (DESIGN PROPOSAL)

**Status:** DESIGN PROPOSAL for review. Proposes, but does **not** implement, the
elimination form for the first-class `command` constructor added in R1-inc1
(syntax) and typed in R1-inc2 (`commit-I`). No `.rs`, `.lean`, `spec/syntax.md`,
or `spec/typing-rules.md` file is edited by this proposal — those are the
lockstep implementation step, gated on approval of this design. Every new rule /
theorem below is stated as **proposed / to be proved**.

Branch `dlc-d/phase0-carve`, HEAD `02835b6`. Reads against the shipped state:
`lean/DLC/Judgment.lean` (`Deriv.commitI`), `lean/DLC/NonInterferenceLR.lean`
(the `.replicated` `LRel` clause + PER lemmas), `lean/DLC/Reduce.lean`,
`lean/DLC/Progress.lean` (`Value`/`CoreTerm`/`progress_aux`),
`lean/DLC/NonInterferenceFundamental.lean` (`fundamental`'s `commitI` case),
`lean/DLC/NonInterferenceTwoRun.lean` (`Observable`), `lean/DLCD/Rsm.lean`
(`applyCommand`/`worldStep`), and `spec/distributed-calculus-design-2026-07.md`
§1.3/§3.1.

---

## 0. Prior art (web-searched 2026-07-23; URLs recorded)

The design problem — *how a boxed/labeled computation is RUN, its label tracked
onto the result type by the eliminator* — has direct, load-bearing prior art.
The shape is standard: **the eliminator moves the modality/label off the value's
type and onto (a) a bound variable and (b) the result type, and the result must
be "protected at" the eliminated label**.

- **Moggi, _Computational λ-calculus and monads_** — the monadic elimination
  `let x = M in N`: from a computation `M : T A` bind `x : A` in a continuation
  `N : T B`; effects cannot leak out of `T`. `runCmd` is the DLC analogue: run a
  `Replicated`-boxed store-transformer and continue at a labeled result.
  <https://www.semanticscholar.org/paper/Computational-lambda-calculus-and-monads-Moggi/f67dec0099505e23e9441a9a567fea1d97ff69f6>
- **Abadi, Banerjee, Heintze, Riecke, _A Core Calculus of Dependency_ (POPL 1999)**
  — DCC's non-standard **bind** rule: eliminating the `T_ℓ` monad requires the
  body type be **"protected at ℓ"**, which is exactly "the result carries ℓ".
  This is the theoretical warrant for `runCmd`'s conclusion being `φ @ ℓ`
  (protected at the eliminated label), and for the noninterference proof shape.
  <https://www.cs.cornell.edu/andru/cs711/2003fa/reading/abadi99core.pdf>,
  <https://dl.acm.org/doi/10.1145/292540.292555>
- **Abadi, _Access Control in a Core Calculus of Dependency_ (ACL-DCC)** —
  `p says φ` as a principal-indexed monad whose elimination protects the result;
  the `commit-I` credential premise is the ACL-DCC discipline made a commit gate.
  <https://users.soe.ucsc.edu/~abadi/Papers/acldcc-acm.pdf>
- **Tang, Hillerström, Lindley, Morris, _Modal Effect Types_ (arXiv 2407.11816)**
  and **_Rows and Capabilities as Modal Effects_ (arXiv 2507.10301)** — the
  let-style modal elimination that **"moves the modality from the type of a value
  to the binding of a variable"**, taking the eliminated modality as an explicit
  index; the direct template for reading `ℓ` off the value's type at the
  eliminator. <https://arxiv.org/pdf/2407.11816>, <https://arxiv.org/pdf/2507.10301>
- **Orchard, Liepelt, Eades, _Quantitative Program Reasoning with Graded Modal
  Types_ (Granule, ICFP 2019)** — graded-modality `elim` (unbox) matches a
  variable's capability against its graded modal type; the label/grade is read
  off the type, not the term. <https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf>
- **Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, _Combining Effects and
  Coeffects via Grading_ (ICFP 2016)** — the graded framework in which
  elimination composes grades; underlies the "label read off the type" choice.
  <https://cs-people.bu.edu/gaboardi/publication/GaboardiEtAlIicfp16.pdf>
- **Bell–LaPadula "no read up"** — *once high data enters the context, every
  subsequent output is tainted at the elevated level.* Running a command
  classified `ℓ` must taint its result at `ℓ`: `runCmd`'s reduct is
  `liftLabel ℓ (…)`, the taint-elevation-on-elimination made operational.
  <https://www.sciencedirect.com/topics/computer-science/lapadula-model>
- **Pistol/Nanevski et al., _Contextual Modal Types for Algebraic Effects and
  Handlers_ (arXiv 2103.02976)** — modal boxing of effectful computations run by
  an eliminator; corroborates the run-the-box shape. <https://arxiv.org/pdf/2103.02976>

**Takeaway that decides §2.** In every reference above the eliminated
label/modality is read off **the value's type**, and the result is **protected
at that label**. That is compositional (works when the boxed value is a
variable) and is what makes the noninterference proof discharge. It rules
*against* recovering the label from the term syntax at the eliminator.

---

## 1. The inc2 knot, precisely (validated)

R1-inc2 (`02835b6`) shipped `Deriv.commitI` (`lean/DLC/Judgment.lean:342-347`):

```
Γₐ;· ⊢ c : issuer says capProp     Γₐ;· ⊢ M : φ ⊃ φ
────────────────────────────────────────────────────────  (commit-I, additive)
Γₐ;· ⊢ command M c ℓ : Replicated (φ ⊃ φ)
```

`command M c ℓ` is a **value** (`Value (command _ _ _) = True`,
`Progress.lean:75`; `step (command …) = none`, no arm in `Reduce.lean`). The
`LRel` clause for `Replicated` is **intro-form / collapsing**
(`NonInterferenceLR.lean:106-120`): both sides `Steps` to a `command` with
`LRel`-related payloads. `fundamental`'s `commitI` case discharges by `.refl`
+ the payload IH (`NonInterferenceFundamental.lean:325-334`).

Three facts make the *design-doc-proposed* elimination unrealizable as written:

1. **`Replicated (φ⊃φ)` is not a function type.** §1.3 proposed
   `(command-β) app (command M c ℓ) s ▷ app M s`. But `command M c ℓ :
   Replicated (φ⊃φ)`, and `app` requires a `φ⊃φ`/`φ⊸φ` head. `app (command …) s`
   is **ill-typed** — there is no `Deriv` for it. The design doc's own `imp-E`
   (`Judgment.lean:95`) cannot fire on a `Replicated`-typed head. **SR HOLE** in
   the proposed rule: the redex is untypable, so "preservation" is vacuous and
   progress is *false* (a well-typed `Replicated` value has no eliminator).

2. **The label `ℓ` is in the TERM, not the TYPE.** `commit-I`'s conclusion
   `Replicated (φ⊃φ)` erases `ℓ`. No elimination can produce a result *at* `ℓ`
   without recovering `ℓ`, and the only place it survives is the `command`
   subterm's third field — invisible to any compositional typing rule (a command
   bound to a variable `x : Replicated (φ⊃φ)` has lost `ℓ` entirely).

3. **The `at φ ℓ` low-branch is unsatisfiable by a command.** inc2 recorded
   that relating commands at `Prop'.at φ ℓ` is unprovable while `command` is a
   non-reducing value: `LRel (at φ ℓ)` at a low label demands both sides
   `Steps` to `liftLabel ℓ _` (`NonInterferenceLR.lean:76-80`), a canonical form
   `command` never exhibits. The label-precision NI gate is therefore **deferred
   / vacuous** today — it can only be made genuine by a *reduction that produces
   a `liftLabel ℓ` form*.

The three are one problem: **elimination, label-tracking, and the NI gate must
be solved together, by a dedicated eliminator whose typing reads `ℓ` off the
value's type and whose reduction emits `liftLabel ℓ`.**

---

## 2. The design

### 2.1 The elimination form — a dedicated `runCmd` eliminator (Option a)

Add one `Term` eliminator:

```lean
-- lean/DLC/Syntax.lean, appended to `inductive Term` (append-only)
| runCmd : Term → Term → Term        -- runCmd cmd store
```
```rust
// crates/dlc-core/src/syntax.rs (PROPOSED mirror)
/// `runCmd(cmd, s)` — run a `Replicated (φ⊃φ)@ℓ` command against a store `s:φ`,
/// applying the boxed transformer and classifying the result at `ℓ`.
RunCmd(Box<Term>, Box<Term>),
```

**Why a new eliminator and not `app` (Option b, rejected).** `app` demands a
`φ⊃φ` head; `command M c ℓ : Replicated (φ⊃φ)@ℓ` is a `Replicated`-modal value.
Reusing `app` is exactly the SR hole of §1(1). The `Replicated` modality must be
*unwrapped by its own eliminator*, precisely as `discharge` unwraps `boxed`,
`sfExtract`/`saysBind` unwrap `says`, and `case` unwraps `or`. `runCmd` is the
`Replicated`-elimination; it is not sugar for application. Neither subterm binds
a variable, so — like `app`/`pair`, unlike `saysBind`/`letTensor` — `shift`/
`substAt` recurse into both fields **without bumping the cutoff** (the cheapest
substitution interaction; `Subst.lean` gains an `app`-shaped case).

No new `Prop'` constructor is needed for the *result*: it is `Prop'.at φ ℓ`,
reusing the shipped `liftLabel`/`at`/`declassify` machinery. (`Prop'` *is*
touched, but for the command's own type — §2.2.)

### 2.2 Where the label lives — indexed `Replicated` (Option i), RECOMMENDED

The label must be recoverable **at the eliminator, compositionally** (so
`runCmd x s` for `x : <cmd type>` a variable still types). Per §0 that forces
the label into the **type of the command**, not its term syntax.

Two type-level placements, and one term-level placement, were weighed:

| | placement | compositional? | keeps inc2 `fundamental` commitI? | cost |
|---|---|---|---|---|
| **(i-a) RECOMMENDED** | `replicated : Prop' → Label → Prop'` (index inc1's ctor); `command M c ℓ : Replicated (φ⊃φ) ℓ` | yes — `ℓ` read off the type | **yes** (`command` stays the value; clause pins its label field) | arity change to `replicated` (non-append-only) + `commit-I` conclusion churn |
| (i-b) rejected | `at (Replicated (φ⊃φ)) ℓ` (wrap in existing `at`) | yes | **no** — `LRel (at _ ℓ)` demands the value `Steps` to `liftLabel ℓ`, which `command` is not; forces the intro term to become `liftLabel ℓ (command M c)` and `command` to drop its label. Bigger churn, breaks inc2. | breaks shipped `fundamental` |
| (ii) rejected | keep `Replicated (φ⊃φ)`; `runCmd` typing reads `ℓ` from a literal `command M c ℓ` scrutinee | **no** — `runCmd x s` untypable when `x` is a bound command variable | yes | snapshot-preserving but non-compositional; contradicts all §0 prior art |

**Recommendation: (i-a).** Make `replicated` label-indexed. It is the only
option that is simultaneously (a) compositional (label off the type, matching
DCC/Modal-Effect-Types/Granule), (b) preserves inc2's working `fundamental`
`commitI` case (the intro value is still `command`, a value), and (c) makes the
NI gate genuine (§2.5). The tradeoff is **snapshot churn**: revising
`replicated`'s arity is *not* append-only and changes the `Prop'` snapshot plus
every `commit-I` conclusion (§6, §7). The cheaper option (ii) is rejected not
because it is unsound but because it yields a strictly weaker theorem — a
`Replicated` value that has passed through *any* abstraction boundary can never
be run — which defeats the point of first-classing.

> Append-only variant of (i-a), if the ruling forbids the arity edit: add a
> **new** ctor `replicatedAt : Prop' → Label → Prop'` and leave inc1's
> `replicated : Prop' → Prop'` in place (unused). This keeps the edit
> append-only at the cost of a dead label-free ctor. Either way `commit-I`'s
> conclusion snapshot changes (it must, to carry `ℓ`) — see §6.

Revised shapes:

```lean
-- lean/DLC/Syntax.lean  (revise inc1's ctor; PROPOSED)
| replicated : Prop' → Label → Prop'

-- lean/DLC/Judgment.lean  Deriv.commitI conclusion (revise; PROPOSED)
Deriv {additive := Γₐ, linear := []}
      (Term.command M c ℓ) (Prop'.replicated (Prop'.imp φ φ) ℓ)
      -- term's label field and the type index are the SAME ℓ (load-bearing, §2.4)
```

### 2.3 The reduction rule(s) (append-only redex list)

`spec/typing-rules.md` §11, appended (PROPOSED); `Reduce.lean` `step` gains one
arm shaped like the `app`/`fst` arms:

```
(runCmd-β)   runCmd (command M c ℓ) s  ▷  liftLabel ℓ (app M s)      -- run + classify
(ξ-runCmd)   V ▷ V'  ⇒  runCmd V s ▷ runCmd V' s                     -- normalize scrutinee
```

```lean
-- Reduce.lean, new arm (call-by-name, scrutinee-position congruence)
| Term.runCmd v s =>
    match v with
    | Term.command m _c l => some (Term.liftLabel l (Term.app m s))   -- credential erased
    | _ => match step v with
           | some v' => some (Term.runCmd v' s)
           | none => none
```

- The credential `c` is **discarded** by `runCmd-β` (checked at typing via the
  `commit-I` premise, erased at reduction — the `discharge`/`boxed` idiom,
  `Reduce.lean:130-149`).
- The label `ℓ` is **preserved into the `liftLabel ℓ` wrapper** — the whole
  point. `ℓ` comes from the `command`'s own field, which `commit-I` ties to the
  type index (§2.2), so it equals the eliminator's result-type label (§2.4).
- `runCmd` is **not** a `Value` (default `_ => False` in `Progress.Value`); it is
  computational core: `CoreTerm (runCmd v s) = CoreTerm v && CoreTerm s`.

**Re-founding `applyCommand`/`worldStep` — in VALUE, this increment.** inc3 does
**not** rewire `lean/DLCD/Rsm.lean`; `applyCommand c s = (reduceWithFuel (app
c.payload s) applyFuel).1` is **byte-unchanged**, because `Rsm.Command.payload`
is the *raw* transformer `M`, not a `Term.command`. What `runCmd-β` establishes
is that the first-class eliminator's operational **core is `app M s`** — the
exact expression `applyCommand` normalizes — plus (i) one extra head step
(`runCmd-β`), absorbed by `applyFuel = 1024 ≫ 1`, and (ii) an outer `liftLabel ℓ`
that is the *new label-tracking*, isolated to the DLC typing/NI layer. Concretely
`(reduceWithFuel (runCmd (command M c ℓ) s) applyFuel).1 = liftLabel ℓ
((reduceWithFuel (app M s) (applyFuel−1)).1)`, i.e. `applyCommand`'s result under
a `liftLabel ℓ` cap. So `applyPrefix`/`deliver`/`worldStep`/
`replicas_converge_on_prefix` and the anti-vacuity witnesses (`Rsm.lean:242-284`)
are **untouched and still green**. Routing `Rsm.applyCommand` *through* `runCmd`
(with the store-label ruling — strip the `liftLabel` cap to byte-preserve the
DLCD witnesses, vs. keep it for a genuinely `at φ ℓ`-typed store) is a **later
increment**, consistent with inc2's explicit deferral of store-type/label
plumbing. **Recommendation: defer; keep Rsm byte-identical this increment.**

### 2.4 Subject reduction closes

`runCmd`'s typing rule (PROPOSED, `Deriv`/`PropDeriv`, additive; append-only
constructor). It reads `ℓ` and `φ` off the scrutinee's `Replicated (φ⊃φ) ℓ`
type — compositional, no term inspection:

```
Γₐ;· ⊢ V : Replicated (φ ⊃ φ) ℓ      Γₐ;· ⊢ s : φ
──────────────────────────────────────────────────────  (runCmd)
Γₐ;· ⊢ runCmd V s : φ @ ℓ
```

Two SR obligations (`SubjectReductionStatement`, `Reduce.lean:190`):

**(ξ-runCmd).** `runCmd V s ▷ runCmd V' s` with `V ▷ V'`. From `runCmd V s : φ@ℓ`
invert `(runCmd)`: `V : Replicated (φ⊃φ) ℓ`, `s : φ`. By SR on the premise
`V' : Replicated (φ⊃φ) ℓ`, so `(runCmd)` re-derives `runCmd V' s : φ@ℓ`. ✓

**(runCmd-β).** `runCmd (command M c ℓ) s ▷ liftLabel ℓ (app M s)`. From
`runCmd (command M c ℓ) s : φ@ℓ` invert `(runCmd)`:
`command M c ℓ : Replicated (φ⊃φ) ℓ` and `s : φ`. Invert `commit-I` on the first
(sole intro for `Replicated`): the command's label field **is** the type index
`ℓ` (§2.2), and `M : φ⊃φ`, `c : issuer says capProp`. Type the reduct:
- `app M s` by `imp-E` in the additive instance (`Γ₁ = Γ₂ = []`, so the rule's
  `shift s 0 Γₐ.length = s`, `Judgment.lean:95-99`): from `M : φ⊃φ`, `s : φ` get
  `app M s : φ`. ✓
- `liftLabel ℓ (app M s)` by `liftLabel` (`Judgment.lean:228-230`): from
  `app M s : φ` get `liftLabel ℓ (app M s) : φ @ ℓ`. ✓

Reduct type `φ @ ℓ` **= the redex's type**. SR closes with no hole. (Crucially,
runCmd-β uses the command's own `ℓ`; `commit-I`'s tying of field-label to
type-index is what makes it the *same* `ℓ` the eliminator promised — remove that
tie and SR opens.)

**Progress.** `progress_aux` (`Progress.lean:178`) gains a `runCmd` case: the
scrutinee IH gives a value or a step. Value at `Replicated (φ⊃φ) ℓ` ⇒ canonical
forms (commit-I is the only intro) ⇒ `command M c ℓ` ⇒ `runCmd-β` fires. A step
⇒ a `runCmd_steps` ξ-witness (the `app_steps` clone) lifts it. ✓

### 2.5 Noninterference — the `at φ ℓ` gate becomes genuine

**Revised `LRel` clause for the indexed `Replicated` (pin the label field):**

```lean
-- NonInterferenceLR.lean, replacing lines 106-120 (PROPOSED)
| .replicated φ ℓ, M, N =>
    ∃ M₁ c₁ M₂ c₂,
      Steps M (Term.command M₁ c₁ ℓ) ∧ Steps N (Term.command M₂ c₂ ℓ) ∧
      LRel ℓLow φ M₁ M₂
```

This is the shipped intro-form clause with the two free label existentials
`ℓ₁,ℓ₂` *replaced by the type index `ℓ`* — a strengthening that is exactly what
lets the `runCmd` case conclude the reduct is `liftLabel ℓ` (not `liftLabel k`
for some unknown `k`). It still discharges `fundamental`'s `commitI` case:
`command M c ℓ : Replicated (φ⊃φ) ℓ`, both sides `.refl` to `command M c ℓ`
(field-label = index `ℓ`), payloads related by `ih_M` — the current proof adapts
by dropping the `ℓ₁/ℓ₂` binders. PER lemmas (`lrel_expand_left/right`,
`lrel_symm`, `lrel_trans`, `NonInterferenceLR.lean:255,311,382,467`) re-prove
mechanically: the `steps_to_value_unique` value-uniqueness step is *simpler*
(the label is fixed, not existential). **[RE-PROVE], mechanical.**

**The new `fundamental` `runCmd` case discharges (and closes the gate).**
For `runCmd V s : φ@ℓ`, IH gives, under related closing environments `γ₁,γ₂`:
- `LRel (Replicated (φ⊃φ) ℓ) V₁ V₂` ⇒ `Steps Vᵢ (command Mᵢ cᵢ ℓ)`,
  `LRel (φ⊃φ) M₁ M₂` (label pinned to `ℓ` by the revised clause);
- `LRel φ s₁ s₂` with `s₁,s₂` closed (the msubst-closes-under-closed-env
  machinery already used by the `tensor` case, `NonInterferenceFundamental.lean`).

Reduce both runs: `runCmd Vᵢ sᵢ →*(ξ-runCmd on Steps Vᵢ)→ runCmd (command Mᵢ cᵢ ℓ)
sᵢ →(runCmd-β)→ liftLabel ℓ (app Mᵢ sᵢ)`. By anti-reduction (`lrel_expand`,
`NonInterferenceLR.lean:331`) it suffices to relate the reducts at `at φ ℓ`:
- **ℓ ⊑ ℓLow (low):** the `at` low-branch (`NonInterferenceLR.lean:76-80`) needs
  `Steps (liftLabel ℓ (app Mᵢ sᵢ)) (liftLabel ℓ mᵢ)` — take `mᵢ = app Mᵢ sᵢ`
  (`.refl`, `liftLabel` is a value) — and `LRel φ (app M₁ s₁) (app M₂ s₂)`, which
  is `LRel (φ⊃φ) M₁ M₂` (the imp/arrow clause) applied to the closed related
  stores `LRel φ s₁ s₂`. ✓ **This is the liftLabel canonical form inc2 said the
  low-branch demanded and a non-reducing `command` could never supply — now
  supplied by `runCmd-β`.**
- **ℓ ⋢ ℓLow (high):** the `at` clause is `True`. The high command's result is
  invisible to the low observer — the label-precision gate, genuine, not
  deferred. ✓

So T3's `at φ ℓ` observability gate is now **live** on the eliminated result:
`Observable` (`NonInterferenceTwoRun.lean:40`) at `at φ ℓ` already requires
`ℓ ⊑ ℓLow`; `runCmd` is the first term whose *reduction* produces the
`liftLabel ℓ` witness that discharges the low side and whose *high* side is
protected — exactly DCC's "body protected at ℓ" and Bell–LaPadula's
taint-elevation-on-run. **[RE-FOUND]** onto a new `fundamental` case.

### 2.6 Realizability / anti-vacuity witness (proposed)

A concrete run: `M = λx:φ. x` (identity transformer), `s = var 0`, `ℓ` any label.
Then `runCmd (command (lam φ (var 0)) c ℓ) (var 0) ▷ liftLabel ℓ (app (lam φ
(var 0)) (var 0)) ▷ liftLabel ℓ (var 0)` — a genuinely `liftLabel`-headed normal
form at `at φ ℓ` (distinct head constructor from the input), so the low-branch of
the NI gate is inhabited, not vacuous. A second witness at a *high* `ℓ` with two
distinct credentials/payloads shows the high branch relates the runs (gate = `True`).

---

## 3. `commit-I` conclusion revision (§2.2, restated for the ledger)

`commit-I` **keeps its premises unchanged** (`c : issuer says capProp`,
`M : φ⊃φ`, additive) and **gains `ℓ` in its conclusion type**:

```
Γₐ;· ⊢ command M c ℓ : Replicated (φ ⊃ φ)  ⟹  Γₐ;· ⊢ command M c ℓ : Replicated (φ ⊃ φ) ℓ
```

The term is byte-identical (`command M c ℓ` already carries `ℓ`); only the
conclusion `Prop'` gains the index. This is consistent with — and the minimal
enabler of — the `runCmd` rule (§2.4), and it realizes the design doc §3.1
intent (`Replicated (φ@ℓ)`) via a *label index on `Replicated`* rather than a
nested `at`, which (i-b, §2.2) would break the shipped `fundamental`. The same
one-index edit applies to `PropDeriv.commitI` (`Decidability.lean:1088`) and
`DerivCrypto.commitI` (`Correspondence.lean:268`).

---

## 4. Impact map (files / inductions inc3 touches)

**A. `replicated` arity + `command` conclusion (the (i-a) edit).** Every
`Prop'`-structural site with a `.replicated` case gains a `Label` argument (all
already have the case from inc1/inc2 — a re-found, not a new case):
- `lean/DLC/Syntax.lean` — `Prop'.replicated` ctor arity. **[snapshot: Prop']**
- `lean/DLC/Decidability.lean` — `Prop'.beq` (`:122`), inference (`:462`),
  `PropDeriv.commitI` (`:1088`) + its recursors (`:1243,1462,1764,1870,2278`).
  **[RE-PROVE, mechanical]** **[snapshot: PropDeriv]**
- `lean/DLC/Judgment.lean` — `Deriv.commitI` conclusion (`:342`).
  **[snapshot: Deriv]**
- `lean/DLC/Correspondence.lean` — `DerivCrypto.commitI` (`:268`) + recursors.
  **[snapshot: DerivCrypto]**
- `lean/DLC/NonInterferenceTwoRun.lean` — `Observable.replicated` (`:49`).
- `lean/DLC/NonInterferenceLR.lean` — `LRel.replicated` clause (`:106`) + the
  four PER/expand lemmas (`:255,311,382,467`). **[RE-PROVE, mechanical]**
- `lean/DLC/NonInterferenceFundamental.lean` — `fundamental.commitI` (`:325`)
  (drop the `ℓ₁/ℓ₂` binders; pinned label). **[RE-FOUND]**

**B. `runCmd` eliminator (append-only `Term` ctor).** Every `Term`-structural
site gains a `runCmd` case (`app`-shaped, non-binder, two subterms):
- `lean/DLC/Syntax.lean` — `Term.runCmd` ctor. **[snapshot: Term]**
- `lean/DLC/Subst.lean` — `shift` (`:69`-shape) + `substAt` (`:127`-shape),
  `app`-shaped (no cutoff bump).
- `lean/DLC/Reduce.lean` — new `step` arm (§2.3).
- `lean/DLC/Progress.lean` — `CoreTerm` (`app`-shape), `Value` (nothing:
  `_ => False`), `progress_aux` new case + a `runCmd_steps` ξ-witness.
  **[snapshot: none — Value/CoreTerm are `def`s, not axioms]**
- `lean/DLC/Judgment.lean` + `lean/DLC/Decidability.lean` — new `Deriv.runCmd` /
  `PropDeriv.runCmd` constructor + inference arm + recursors.
  **[snapshot: Deriv, PropDeriv]**
- `lean/DLC/Correspondence.lean` — `DerivCrypto.runCmd` + `allSigsVerify`
  (`:115`-shape). **[snapshot: DerivCrypto]**
- `lean/DLC/NonInterferenceLR.lean` — ξ-congruence `step_runCmd_congr` + expand
  lemma cases (result type `at`, no new `Prop'` case needed).
- `lean/DLC/NonInterferenceFundamental.lean` — new `runCmd` `fundamental` case
  (§2.5). `lean/DLC/NonInterferenceEnv.lean` — `ClosedAbove`/`msubstAt`/`usesVar`
  `runCmd` cases (`app`-shape, cf. `:218,:1041`).
- `lean/DLC/ObligationSoundness.lean` — `pendingObligations (runCmd v s) =
  pendingObligations v ++ pendingObligations s` (`app`-shape, cf. `:83`).

**C. Spec + Rust mirrors (PROPOSED, not edited here; the implementation step).**
`spec/syntax.md`, `spec/typing-rules.md` §11+§13, `crates/dlc-core/src/syntax.rs`,
`crates/dlc-core/src/{judgment,reduce,decide}.rs`, `scripts/check-drift.sh`
(Aeneas regen).

**D. DLCD — UNTOUCHED this increment** (`lean/DLCD/*`). `applyCommand`/`worldStep`
byte-identical (§2.3); the RSM re-founding onto `runCmd` is a later increment.

**Axiom snapshots.** Byte-**changed**: `Term` (append: `runCmd`), `Prop'`
(revise: `replicated` arity), `Deriv`/`PropDeriv`/`DerivCrypto` (revise:
`commitI` conclusion; append: `runCmd`). Byte-**unchanged**: everything not
above, incl. all DLCD snapshots and all non-`command`/`runCmd` DLC rules. Rule
IDs are **append-only** (`runCmd`); the sole non-append-only edit is
`replicated`'s arity + `commitI`'s conclusion (unavoidable for label-in-type;
the append-only `replicatedAt` variant in §2.2 trades a dead ctor to avoid the
arity churn but still changes `commitI`'s conclusion snapshot). Green-to-green:
every affected proof is [RE-PROVE, mechanical] or [RE-FOUND]; **no [RE-PROVE]
that weakens a statement**, and no `sorry`.

---

## 5. SR-soundness gate — self-audit

- **`runCmd-β` reduct typeable at the redex type?** Yes — `liftLabel ℓ (app M s)
  : φ@ℓ` = redex type, via `imp-E` (additive) + `liftLabel` (§2.4). **Closed.**
- **`ξ-runCmd` reduct typeable?** Yes — SR on the scrutinee premise (§2.4).
  **Closed.**
- **Rejected `app (command…) s` (design doc §1.3)?** SR hole — redex untypable
  (§1(1)). **Not adopted.**
- **Rejected (i-b) `at (Replicated) ℓ`?** Breaks shipped `fundamental` (§2.2).
  **Not adopted.**
- **Label identity `field = index`?** Guaranteed by `commit-I` (§2.2); it is the
  hinge of both the β SR obligation and the `fundamental` `runCmd` case. If a
  future rule introduces `Replicated _ ℓ` values whose field ≠ `ℓ`, both open —
  flagged for the implementer to keep `commit-I` the sole `Replicated` intro.

---

## 6. Migration / green-to-green

1. `spec/syntax.md` + `spec/typing-rules.md` first (`runCmd`; `Replicated`
   label index; `commit-I` conclusion; `runCmd-β`/`ξ-runCmd`).
2. Rust mirror (`syntax.rs`, `judgment.rs`, `reduce.rs`, `decide.rs`).
3. Lean mirror per the §4 impact map.
4. `scripts/check-drift.sh` (Aeneas regen clean).
5. Re-prove the [RE-PROVE, mechanical] sites; re-found the [RE-FOUND] cases;
   refresh the 5 changed axiom snapshots (`Term`, `Prop'`, `Deriv`, `PropDeriv`,
   `DerivCrypto`); `make ledger` green; anti-vacuity witnesses (§2.6) added.

---

## 7. Open questions for ruling

1. **(i-a) arity revision vs. append-only `replicatedAt`.** Recommend the arity
   revision (`replicated : Prop' → Label → Prop'`) — cleaner, one ctor — accepting
   the non-append-only `Prop'` snapshot edit. The `replicatedAt` variant keeps the
   edit append-only at the cost of a dead label-free ctor. Which discipline wins
   here — minimal ctor count or strict append-only? (Either way `commit-I`'s
   conclusion snapshot changes.)
2. **Rsm re-founding timing.** Recommend **deferring** the `applyCommand`-through-
   `runCmd` rewire (keep DLCD byte-identical this increment). When it lands, rule:
   **strip** the outer `liftLabel ℓ` at the Rsm boundary (byte-preserve the DLCD
   convergence witnesses; label stays a DLC-layer concern) vs. **keep** it (store
   becomes genuinely `at φ ℓ`-typed; DLCD witnesses churn)?
3. **`query`/`Converges` scope.** inc3 delivers `runCmd` (run the transformer
   against a store — the `applyCommand` analogue). The design doc's `query`/
   `Converges` read-back eliminator (§2.2/§3.4) is a *different* elimination
   (read a replicated value gated by a convergence witness). Confirm it stays out
   of inc3 (later increment), so inc3's `Replicated` elimination is `runCmd` only.
4. **Result type `φ @ ℓ` vs. `(φ⊃φ) @ ℓ`.** `runCmd` runs the endomorphism and
   returns the *updated store* at `φ@ℓ` (recommended — matches `applyCommand`
   producing a store). An alternative eliminator could return the transformer
   itself at `(φ⊃φ)@ℓ` (a "declassified read" of the boxed function). Confirm the
   store-returning form is the intended `command` semantics.
5. **Credential erasure.** `runCmd-β` discards `c` (checked at typing). Confirm
   this matches the `discharge`/`boxed` evidence-erasure discipline and no
   downstream (audit-log) consumer needs `c` retained in the reduct.
```
