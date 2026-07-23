import DLC.Subst
import DLC.CarveCtx
import DLC.Reduce

/-! # CARVe-migrated judgment — real `Term`/`Prop'` fragment + weakening-in-the-middle
     (DLC-D Phase 0, increment 2: leftover var rule + the four modal `CJoin` rules)

This lifts the machine-checked `CarveProto` prototype off its toy `Ty`/`Tm`
entry types onto DLC's **real** `Term`/`Prop'` and the real `DLC.shift`, over
the promoted resource-vector context infrastructure in `DLC.CarveCtx`
(`DLC.Carve.{Ctx, CJoin, cjoin_split, cjoin_insert, zeroed}`). It is the first
concrete step of the CARVe migration (`theorem-status.json::linear_lever_L1`
L3/L4): a context is ONE usage-tagged vector, a "split" is an elementwise
`CJoin`, so **no rule carries a `shift` in its conclusion** and positions never
move — which is exactly what lets weakening-in-the-middle (`cderiv_shift`)
go through in the `tensorE`/`letTensor` case that the current
`{additive, linear : List}` representation cannot.

## Prior art (web-searched 2026-07-22; this IS a known-good representation)
The CARVe context is the usage-vector context of **Quantitative Type Theory**;
`Mult = {zero, one, many}` is the semiring `Q`, `CJoin` is context addition.
- McBride, *I Got Plenty o' Nuttin'* (2016): usage-annotated contexts with
  `Q = {0,1,ω}` — but his judgment FAILS the substitution property (= DLC's
  open L4). https://link.springer.com/chapter/10.1007/978-3-319-30936-1_12
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018): the
  fix — in the semiring usage-vector formulation **weakening and substitution
  are admissible** (= L3 + L4). https://bentnib.org/quantitative-type-theory.pdf
- Wood & Atkey, *A Framework for Substructural Type Systems* (ESOP 2022): a
  mechanized (Agda) technique — linear-algebra-over-semirings + kits/traversals
  giving generic renaming/substitution/linearity-checking; splits are
  elementwise semiring joins, exactly `CJoin`.
  https://bentnib.org/quant-framework.html
- Wood & Atkey, *A Linear Algebra Approach to Linear Metatheory*
  (arXiv:2005.02247): the metatheory method to mirror for L4.
So L4 is a KNOWN-SOLVABLE result in this representation, not a research gamble;
this increment proves the L3-shaped keystone (weakening-in-the-middle) on the
real judgment fragment, and the substitution lemma (L4) mirrors Wood–Atkey.

## Scope of this increment (increment 2 — honest)
The fragment now covers `var`, `lam`(imp-I), `app`(imp-E), `tensorIntro`,
`letTensor`(tensor-E) AND the four modal multiplicative rules — `saysE`,
`delegate`, `discharge`, `letSaysE` — each migrated off `linear := Γ₁ ++ Γ₂`
onto an elementwise `CJoin`, so NONE carries a `shift` in its conclusion.
`cderiv_shift` (weakening-in-the-middle) is proved over ALL nine constructors.

**The linear-usage (leftover) side condition is now PROVED, not omitted.**
`CDeriv.var` carries `AllZeroExcept Γ i` — the leaf demands exactly position
`i`, and every OTHER hypothesis carries the consumed tag `Mult.zero`. This is
the "usage-context" variable rule (a basis vector) of Wood–Atkey and the
"leftover" var rule of Allais / Zalakain–Dardha, specialised to the
`{zero, one, many}` resource algebra (= QTT's `Q`; Atkey LICS 2018). The var
case of `cderiv_shift` re-derives `AllZeroExcept` for the inserted-block
context via `allZeroExcept_insert`: the inserted `zeroed Γm` block is
all-`zero` (so trivially unused) and the `Γl`/`Γr` positions map from the
original by the same `getElem?_append_left/right` + `zeroed_length` arithmetic
as the index shift.

The full-judgment migration (the remaining ~30 `Deriv` constructors) and the
substitution lemma (L4, mirroring Wood–Atkey's linear-algebra metatheory) are
subsequent increments. Every rule that CAN migrate faithfully at this point
HAS been migrated and proved; nothing here is deferred with a `sorry`.

## Scope of increment 3a — ADDITIVE (L3) substitution preservation
`cderiv_substA` is now PROVED over ALL NINE constructors (`var`, `impI`, `impE`,
`tensorI`, `tensorE`, `saysE`, `delegate`, `discharge`, `letSaysE`): substituting
`N : φ` for the ADDITIVE (`Mult.many`) hypothesis at position `Γl.length`
preserves `CDeriv`, dropping that position — the resource-vector mirror of
`DLC.Decidability`'s `propDeriv_substAt`. Because the discharged hypothesis is
`many` (unrestricted → duplicable/discardable), the replacement `N` is required
to be RESOURCE-FREE: typed under the all-`zero` context `zeroed Γr`. This is the
faithful QTT condition (Atkey, LICS 2018): an unrestricted variable's filler
must itself use no linear resources. The `var`-hit case discharges `N` into the
leaf via `cderiv_shift` (0-use-variable weakening — all a Wood–Atkey kit needs);
each `CJoin` premise is routed by `cjoin_split_cons`/`mjoin_ne_one` where the
hole tag is `zero` (routed away) or `many` (used). `substAt`'s per-binder depth
bookkeeping (`+1` for `impI`/`saysE`/`letSaysE`, `+2` for `tensorE`) is matched
by extending `Γl` under each binder — no shift-commutation lemma needed, since
CARVe conclusions carry no shift.

**Now DONE in increment 3b (see below):** LINEAR (`Mult.one`) substitution, where
`N`'s context does NOT vanish but `CJoin`-MERGES with the leftover of `M`
(usage-vector addition, the linear-algebra case of Wood–Atkey arXiv:2005.02247).
That case needs `N` typeable under an arbitrary (non-`zeroed`) context `Δ` and the
result context to be the join `Γr ⊕ Δ`, not the additive "drop the position".

## Scope of increment 3b — LINEAR (`one`) substitution preservation (true L4)
`cderiv_substL` is PROVED over ALL NINE constructors: substituting `N : φ`, with
its OWN resource vector `Δ`, for the LINEAR (`Mult.one`) hypothesis at position
`Γl.length` preserves `CDeriv`, `CJoin`-MERGING `Δ` into `M`'s leftover at the
positions after the hole:
  `CDeriv (Γl ++ (φ, one) :: Γr) M ψ → CDeriv Δ N φ → CJoin Γr Δ Γr' →`
  `CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ`.
This is the CUT rule and the linear-algebra substitution step of Wood–Atkey
(arXiv:2005.02247) on the real `Term`/`Prop'`. Its content beyond 3a:
- **routing.** A `one` hole splits (`cjoin_split_cons`) into `MJoin m₁ m₂ one`,
  which by `mjoin_one_not_shared` has ONLY the `zl`/`zr` shapes: the hole lands
  entirely on ONE premise (recurse `cderiv_substL_aux`, re-routing `Δ`), while
  the sibling carries it at `zero` and is dropped by `cderiv_dropZero_aux`
  (a proved strengthening: a `zero`-tagged hypothesis is never referenced, so
  `substAt` never PLACES `N` there). The route is chosen on the tag DATA
  (`by_cases … = one`), since an `MJoin` proof cannot eliminate into the
  `Type`-valued derivation.
- **merge.** Re-routing `Δ` past the surviving premise's leftover is the
  partial-commutative-monoid REASSOCIATION `A ⊕ (B ⊕ D) = (A ⊕ B) ⊕ D`
  (`cjoin_reassoc`, elementwise `mjoin_reassoc`) — the linear-algebra step.
- **the hit.** At the single `var` leaf that consumes the hole (a `one` at any
  OTHER position violates `AllZeroExcept`, so the hit is FORCED), `AllZeroExcept`
  collapses the leftover `Γr` to all-`zero`, whence `cjoin_left_all_zero` makes
  the merge `Γr'` equal to `Δ` exactly — `N` brings all resources at the hole —
  and `cderiv_shift` (0-use weakening by `zeroed Γl`) places `shift N Γl.length 0`.

**Not attempted (honestly deferred):**
- **OPEN ADDITIVE substitution** (a `many` hole filled by an `N` with a
  non-`zeroed` `Δ`) does NOT fall out of the linear lemma: a `many` hypothesis
  may be used 0..n times, so `N`'s resources would have to be SCALED by `many`
  (duplicated), which is sound only if `Δ` is itself duplicable (all-`zero` or
  all-`many`). The linear (`one`) multiplicity is exactly the case where usage
  ADDS without duplication — the merge here is `CJoin` (`+`), not an
  `n`-fold copy. Subject reduction (increment 4) for a `many`-binder β-redex
  will need that scaled-duplicable variant separately; the `CJoin`-merge proved
  here is the technique that generalises 3a's closed-additive case to open for
  the `one` binders (`tensorE`), which is the load-bearing β-redex.

`#print axioms cderiv_substL` = `#print axioms cderiv_dropZero_aux` =
`[propext, Classical.choice, Quot.sound]` (dropZero: `[propext, Quot.sound]`);
no `sorryAx`, no `native_decide`. `CarveJudgmentChecks.substL_antivacuity_example`
exercises the merge on a real derivation (an `N` consuming a live linear
resource, joined into `M`'s leftover).

`#print axioms cderiv_substA` = `[propext, Classical.choice, Quot.sound]` (no
`sorryAx`, no `native_decide`); likewise `cderiv_shift`.

## Scope of increment 3c — OPEN ADDITIVE (`many`) substitution, SCALED
`cderiv_substM` is PROVED over ALL NINE constructors: substituting `N : φ` —
carrying its OWN OPEN resources `Δ` — for the ADDITIVE (`Mult.many`) hypothesis
at position `Γl.length`, `CJoin`-MERGING `Δ` into `M`'s leftover
(`CJoin Γr Δ Γr'`). This retires the "OPEN ADDITIVE substitution … not attempted"
deferral fenced in increment 3b, for the DUPLICABLE `Δ`.

- **What's proved.** `CDeriv (Γl ++ (φ,many)::Γr) M ψ → CDeriv Δ N φ → NoOne Δ →
  CJoin Γr Δ Γr' → CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ`, all nine rules.
  The QTT-faithful form `cderiv_substM_scaled` takes `N` typed under
  `scaleCtx Mult.many Δ` and merges that — the Atkey (LICS 2018) "scale the
  substituend's usage by the binder multiplicity, then add" — deriving `NoOne`
  automatically (`noOne_scaleCtx_many`).
- **The scaling/soundness note.** A `many` binder may duplicate `N`, so any
  LINEAR (`one`) resource `N` consumes would be copied — unsound. `mscale many`
  BUMPS `one → many` (`ω·1 = ω`); the merge at a shared `many` hole uses
  `MJoin many many many` (idempotent copy). The `NoOne Δ` premise is not a
  weakening but the soundness condition: it excludes exactly the `one` tags on
  which bumping would be unsound, so `scaleCtx Mult.many Δ = Δ` there
  (`scaleCtx_many_of_noOne`). New kit: `mjoin_dup` (elementwise `(many,many)`
  duplication) and `cjoin_dup_reassoc` (route `Δ` into BOTH `CJoin` branches);
  the `(zero,·)`/`(·,zero)` splits reuse 3b's `cjoin_reassoc`/`cderiv_dropZero_aux`.
- **Honestly deferred.** The FULL scaled statement for an `N` whose `Δ` contains
  LIVE `one` tags is NOT provable as stated (retyping `N` from `Δ` to
  `scaleCtx many Δ` bumps `one → many`, the unsound direction) — it is not a
  gap in this proof but a genuine side condition of QTT; `cderiv_substM_scaled`
  is the honest form (it demands `N : scaleCtx many Δ`, already one-free). This
  is the variant increment-4 subject reduction consumes for the `many`-binder
  β-redexes (`imp`/`says`/`delegate`/`discharge`); `tensorE`'s `one`-binder
  β-redex is 3b's `cderiv_substL`.

`#print axioms cderiv_substM` = `#print axioms cderiv_substM_scaled` =
`[propext, Classical.choice, Quot.sound]`; `cjoin_dup_reassoc`/`mjoin_dup`
depend on NO axioms. No `sorryAx`, no `native_decide`.
`CarveJudgmentChecks.substM_antivacuity_example` exercises the merge with an
OPEN, non-vanishing, duplicable `Δ = [(atom 0, many)]`.

## Prior art for the leftover var rule (web-searched 2026-07-22)
- Allais, *Typing with Leftovers — a mechanisation of IMALL* (TYPES 2017):
  input/output usage contexts, threading linear resources without context
  splits. https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2017.1
- Zalakain & Dardha, *π with Leftovers: A Mechanisation in Agda* (FORTE 2021):
  leftover typing over a general usage algebra covering shared/graded/linear.
  https://arxiv.org/pdf/2005.05902
- Wood & Atkey, *A Framework for Substructural Type Systems* (ESOP 2022): the
  usage-context var rule as a basis vector; splits are semiring `∗`/`×`.
  https://strathprints.strath.ac.uk/79767/1/Wood_Atkey_ESOP_2022_A_framework_for_substructural_type_systems.pdf
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018): the
  QTT variable rule over the usage semiring `Q`.
  https://bentnib.org/quantitative-type-theory.pdf

## Scope of increment 4a — subject reduction (preservation) for `CDeriv`
`cderiv_subject_reduction : CDeriv Γ M ψ → NoOne Γ → step M = some M' →
CDeriv Γ M' ψ`, over DLC's real deterministic `step` (`DLC.Reduce`), proved for
ALL NINE constructors (the full induction; see the detailed section header above
`cderiv_subject_reduction`). **Which redexes preserve typing:**
- **tensor-E-β** (`letTensor (tensorIntro a b) B`): the LINEAR load-bearing
  redex — `cderiv_shift` + `cderiv_substL` TWICE + `cjoin_reassoc`. UNCONDITIONAL.
- **imp-β** (`app (lam φ B) N`): preserves typing IFF `N`'s context is
  DUPLICABLE. On the `NoOne Γ` fragment this is automatic (`NoOne` propagates
  through `CJoin` and `step` never crosses a binder), so the top-level theorem is
  unconditional on that fragment; `cderiv_imp_beta` states the standalone
  characterisation `CDeriv Γ (subst B N) ψ` under the exact side condition
  `NoOne Γ₂`.
- **modal head redexes** (`saysE`/`letSaysE`/`delegate`/`discharge` extraction):
  never fire — their scrutinee's intro form (`sign`/`boxed`) is ABSENT from
  `CDeriv`, so the head branch closes on the uninhabited scrutinee derivation.
- **ξ-congruence** (every elimination): IH on the stepped sub-term. Value/frozen
  subjects (`var`, `impI`, `tensorI`) give `step = none`.

**The imp-β soundness FINDING (side condition, not hidden).** `impI` binds a
`many` (unrestricted) hypothesis but `impE` admits an argument with ARBITRARY
(incl. `one`) resources. So an additive-`⊃` β-redex DUPLICATES its argument, and
a LINEAR argument is copied — unsound. Concretely `(λ^many x. x ⊗ x) N` with `N`
using a `one` resource is well-typed but reduces to the ill-typed `N ⊗ N` (a
`one` cannot split into two non-zero summands — `mjoin_one_not_shared`). Hence
imp-β preservation genuinely FAILS without `NoOne` on the argument; the fragment
`NoOne Γ` and the lemma `cderiv_imp_beta`'s `NoOne Γ₂` are the exact, honest
side conditions. Reading: a linear argument belongs to a linear function type
(`⊸`, one-binder), not to `imp` (`⊃`, many-binder) — the QTT scale-then-add
discipline (`cderiv_substM_scaled`).

`#print axioms cderiv_subject_reduction` = `#print axioms cderiv_imp_beta` =
`[propext, Classical.choice, Quot.sound]` (`noOne_cjoin`: `[propext]`); no
`sorryAx`, no `native_decide`. `CarveJudgmentChecks.subjectReduction_impBeta_example`
and `subjectReduction_tensorBeta_example` exercise both firing redexes on real,
inhabited derivations.

Prior art (web-searched 2026-07-22): subject reduction for linear/graded calculi
= substitution lemma per redex, with distinct linear (usage adds) and
unrestricted (usage scales then adds) substitution lemmas.
- Atkey, LICS 2018 (as above): substitution scales usage by the binder
  multiplicity; subject reduction follows.
- Wood & Atkey, *A Linear Algebra Approach to Linear Metatheory* (arXiv:2005.02247):
  linear systems fail naive substitution; the environment method is the fix.
  https://arxiv.org/abs/2005.02247
- "Subject Reduction — an overview" (ScienceDirect): subject reduction of linear
  typing follows from the Linear Substitution Lemma, per redex.
  https://www.sciencedirect.com/topics/computer-science/subject-reduction

## Scope of increment DLC-D "DILL" — the principled fix (UNCONDITIONAL SR)
Increment 4a exposed the imp-β soundness FINDING: DLC's `⊃` binds a `many`
(duplicable) hypothesis but `impE` admitted an argument with ARBITRARY (incl.
LINEAR `one`) resources, so a `⊃`-β redex could DUPLICATE a linear argument —
preservation held only on a `NoOne Γ` fragment. This increment removes that
fragment by adopting the **Dual Intuitionistic Linear Logic / Linear–Non-Linear**
discipline of Barber–Plotkin and Benton: TWO function spaces, each with its own,
sound β.
- **Tightened `⊃`** (non-linear arrow). `CDeriv.impE` now carries a side
  condition `hdup : NoOne Γ₂` — the argument's context must be DUPLICABLE. A
  `many`-binder may only take a duplicable argument, so `⊃`-β is sound via
  `cderiv_substM` (which needs exactly `NoOne` on the substituend) with NO
  ambient hypothesis. The extra hypothesis is re-threaded through the `impE`
  cases of `cderiv_shift` and all three substitution lemmas (each re-establishes
  `NoOne` of the argument's new context from the stored `hdup` via the
  `NoOne` kit: `noOne_append`/`noOne_zeroed`/`noOne_cjoin_merge`/`noOne_drop_middle`).
- **Added `⊸`** (linear arrow, `Prop'.lolli`). `CDeriv.lolliI` binds a LINEAR
  `(φ, one)` hypothesis and concludes `Prop'.lolli φ ψ`; `CDeriv.lolliE` is linear
  application with an UNRESTRICTED argument (arbitrary `Γ₂`, no side condition).
  DLC has **no distinct linear-lambda/linear-app syntax** — `Term` carries only
  `lam`/`app` — so `⊸` SHARES `Term.lam`/`Term.app` with `⊃`, distinguished ONLY
  by typing, matching the real `step`'s single β-redex shape
  `app (lam _ body) arg ▷ subst body arg`. `⊸`-β is sound UNCONDITIONALLY via the
  linear cut `cderiv_substL` (usage ADDS, never duplicates).
- **THE PAYOFF.** `cderiv_subject_reduction' : CDeriv Γ M ψ → step M = some M' →
  CDeriv Γ M' ψ` holds with **NO `NoOne Γ` hypothesis** — every β-case is sound
  for ALL `Γ`: imp-β takes its `NoOne Γ₂` straight from the tightened `impE`
  node, lolli-β and tensor-β are unconditional linear cuts. 4a's `NoOne Γ`
  theorem is retained as a trivial corollary (`cderiv_subject_reduction`). The
  reduction case-split on which introduction typed the function (Barber–Plotkin's
  subject-reduction structure: linear function → linear substitution; non-linear
  function → scaled/duplicable substitution) is realised by `cases dM` selecting
  `impI` (→ `cderiv_substM`) vs `lolliI` (→ `cderiv_substL`) on the arrow's `Prop'`.
`#print axioms` on every new/changed theorem (`cderiv_subject_reduction'`,
`cderiv_subject_reduction`, `cderiv_imp_beta`, `cderiv_lolli_beta`, `cderiv_shift`,
`cderiv_substA/L/M`) = `[propext, Classical.choice, Quot.sound]`; the `NoOne` kit
`[propext]`/`[propext, Quot.sound]`; no `sorryAx`, no `native_decide`.
`CarveJudgmentChecks.subjectReduction_lolliBeta_example` is a real `⊸`-typed
redex `(λ^one x. x) N ▷ N` preserving typing with a LIVE linear argument, the
exact CONTRAST to `subjectReduction_impBeta_example`'s tightened-`⊃` redex.

Prior art (web-searched 2026-07-22): the two-function-space / dual-context design.
- Barber, *Dual Intuitionistic Linear Logic* (ECS-LFCS-96-347, 1996): a single
  judgement over a DUAL context — a cartesian/intuitionistic zone (weakening +
  contraction) and a linear zone (neither) — with both an intuitionistic arrow
  and the linear `⊸`; subject reduction splits by the zone of the substituted
  variable (intuitionistic vs linear substitution).
  http://www.lfcs.inf.ed.ac.uk/reports/96/ECS-LFCS-96-347/
- Benton, *A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models*
  (CSL 1994, LNCS 933 pp.121–135): LNL — linear and non-linear (cartesian)
  logics on an equal footing connected by a monoidal adjunction; the `!` modality
  decomposes into the adjunction between the two. The `⊃` (duplicable) vs `⊸`
  (linear) split here is the term-level shadow of that adjunction.
  https://link.springer.com/chapter/10.1007/BFb0022251
- nLab, *linear–non-linear logic*: https://ncatlab.org/nlab/show/linear-non-linear+logic
- Atkey, *QTT* (LICS 2018) & Wood–Atkey (arXiv:2005.02247): the substitution
  lemmas the two β-cases consume — scale-then-add for `many`, add for `one`.

## Scope of increment DLC-D "progress" — the second half of type soundness
`cprogress : CDeriv [] M ψ → CValue M ∨ ∃ M', step M = some M'`. A CLOSED,
well-typed `CDeriv` term is a value or takes a deterministic `step`. Together
with the UNCONDITIONAL `cderiv_subject_reduction'` (preservation) this is TYPE
SOUNDNESS for the CARVe fragment: a closed well-typed term never gets stuck.
Mirrors `DLC.Progress.progress` (`lean/DLC/Progress.lean`).
- **Fragment / side condition.** `Γ = []` — the EMPTY resource-vector context,
  the `NoOne`/empty-linear closedness condition. It is the CARVe analogue of
  DLC's `PropDeriv [] M φ`. Under it, `CJoin Γ₁ Γ₂ []` forces `Γ₁ = Γ₂ = []`
  (`cjoin_nil`) so every scrutinee sub-context is again empty (IH applies), and
  the `var` leaf is VACUOUS (`[][i]? = none`). This closedness is LOAD-BEARING:
  a bare `var` is genuinely STUCK (`step = none`, not a value) — the right-reason
  bite confirmed the `var` case REDs the instant closedness is dropped.
- **Values (`CValue`).** `CDeriv`'s ONLY introduction terms are `lam`
  (`impI`/`lolliI`) and `tensorIntro` (`tensorI`); `says`/`boxed` have NO intro
  in `CDeriv`. So `CValue = {lam, tensorIntro}`, the restriction of `DLC.Value`
  to the fragment's intros.
- **Canonical forms (inline inversion).** A `CValue` of type `imp`/`lolli` is a
  `lam` (imp-β / lolli-β fire); of `tensor` is a `tensorIntro` (tensor-E-β fires).
  For the modal eliminations (`saysE`/`letSaysE`/`delegate`/`discharge`) there is
  NO closed value of type `says`/`boxed`, so their head redex never fires — but
  the scrutinee, closed and not a value (inversion of a `lam`/`tensorIntro`
  derivation at a `says`/`boxed` type is vacuous), ALWAYS ξ-steps. Hence NO stuck
  term on the closed fragment. All 11 constructors covered, no side condition
  beyond `Γ = []`, no `sorry`.
- `#print axioms cprogress` = `[propext]` (fewer than the permitted
  `[propext, Classical.choice, Quot.sound]`); `cprogress_aux` = `[propext]`;
  `cjoin_nil` depends on NO axioms. No `sorryAx`, no `native_decide`.
  `CarveJudgmentChecks` exercises `cprogress` on a real closed REDEX (shown to
  take the step branch, reduct exhibited by `rfl`) and a real closed VALUE (shown
  to take the value branch, stepping refuted by `step = none`).

Prior art for progress (web-searched 2026-07-22): "a well-typed closed term is a
value or steps", by induction on the derivation + a canonical-forms lemma
characterising well-typed closed values by type.
- PLFA, *Properties: Progress and Preservation*: https://plfa.github.io/Properties/
  (mirror https://plfa.inf.ed.ac.uk/Properties/) — `Progress` = `step ⊎ done`;
  `Canonical V ⦂ A` (arrow → lambda); induction on `∅ ⊢ M ⦂ A`.
- Software Foundations (PLF), *StlcProp — Progress*:
  https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html — the same
  progress + canonical-forms decomposition.
- DLC's own `DLC.Progress.progress` (`lean/DLC/Progress.lean`): the
  `Value M ∨ ∃ M', step M = some M'` shape and the
  `cases scrutinee <;> first | False.elim | cases derivation` canonical-forms
  idiom this increment mirrors onto `CDeriv`.
-/

namespace DLC

open DLC.Carve (Mult MJoin CJoin zeroed zeroed_length cjoin_split cjoin_insert)

/-- **The linear-usage (leftover) side condition.** At a `var` leaf the used
hypothesis sits at position `i`; every OTHER position must already carry the
consumed tag `Mult.zero`. This is the usage-context variable rule of
Wood–Atkey (the used position is a basis vector; the rest is the zero vector)
and the leftover var rule of Allais / Zalakain–Dardha, specialised to
`Mult = {zero, one, many}`. It is what makes a linear (`one`) hypothesis
un-duplicable at a leaf: a `one` at a position other than `i` would violate it. -/
def AllZeroExcept (Γ : Carve.Ctx Prop') (i : Nat) : Prop :=
  ∀ j p, j ≠ i → Γ[j]? = some p → p.2 = Mult.zero

/-- **Duplicability predicate.** `Δ` carries no LINEAR (`one`) tag — every entry
is `zero` or `many`, so `Δ` can be discarded and copied freely (`CJoin Δ Δ Δ`
holds elementwise). This is exactly the condition that makes substituting `N`
for a `many` (unrestricted `⊃`) binder sound: a `many` binder may duplicate `N`,
so `N`'s resources must themselves be duplicable. Defined BEFORE `CDeriv` because
the tightened `impE` (DILL increment) carries it as a side condition on the
argument's context. -/
def NoOne (Δ : Carve.Ctx Prop') : Prop := ∀ p ∈ Δ, p.2 ≠ Mult.one

/-- The CARVe-migrated derivation, on the real `Term`/`Prop'`, over a resource-
vector context `DLC.Carve.Ctx Prop' = List (Prop' × Mult)`. Every elimination
rule JOINS (`CJoin`) instead of splitting `Γ₁ ++ Γ₂`, so — unlike `DLC.Deriv` —
**no constructor carries a `shift` in its conclusion**. -/
inductive CDeriv : Carve.Ctx Prop' → Term → Prop' → Type where
  /-- `var` — position lookup; the used hypothesis is non-`zero`, and EVERY
  other position is consumed (`AllZeroExcept`). The leftover/usage-context
  variable rule specialised to `Mult`. -/
  | var {Γ : Carve.Ctx Prop'} {i : Nat} {φ : Prop'} {m : Mult}
      (h : Γ[i]? = some (φ, m)) (hm : m ≠ Mult.zero) (hz : AllZeroExcept Γ i) :
      CDeriv Γ (Term.var i) φ
  /-- `imp-I` (`lam`) — the bound hypothesis is additive (`many`); real
  `Term.lam` carries its domain type. `shift`'s `lam` clause uses `cutoff + 1`. -/
  | impI {Γ : Carve.Ctx Prop'} {φ ψ : Prop'} {M : Term}
      (d : CDeriv ((φ, Mult.many) :: Γ) M ψ) :
      CDeriv Γ (Term.lam φ M) (Prop'.imp φ ψ)
  /-- `imp-E` (`app`) — the context JOINS; no shift in the conclusion. **DILL
  increment: `⊃` is the NON-LINEAR (`many`-binder, additive) arrow, so its
  argument may be DUPLICATED by β-reduction; the side condition `hdup : NoOne Γ₂`
  restricts the argument to a DUPLICABLE context (no live linear resource). This
  is exactly what makes `⊃`-β sound via `cderiv_substM` (which needs `NoOne` on
  the substituend). A linear argument belongs to `⊸` (`lolliE`), not here. -/
  | impE {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M (Prop'.imp φ ψ)) (dN : CDeriv Γ₂ N φ)
      (hj : CJoin Γ₁ Γ₂ Γ) (hdup : NoOne Γ₂) :
      CDeriv Γ (Term.app M N) ψ
  /-- `lolli-I` (`⊸`-I) — the LINEAR arrow introduction (DILL increment). Binds
  a LINEAR (`one`) hypothesis and concludes `Prop'.lolli φ ψ`. Shares the term
  form `Term.lam` with `impI` (DLC has no distinct linear-lambda syntax — the two
  arrows are distinguished ONLY by typing), so `shift`/`subst` treat it exactly
  like `impI`. -/
  | lolliI {Γ : Carve.Ctx Prop'} {φ ψ : Prop'} {M : Term}
      (d : CDeriv ((φ, Mult.one) :: Γ) M ψ) :
      CDeriv Γ (Term.lam φ M) (Prop'.lolli φ ψ)
  /-- `lolli-E` (`⊸`-E) — LINEAR application (DILL increment). The context JOINS;
  the argument `N` is UNRESTRICTED (arbitrary `Γ₂`, including live `one` tags) —
  a linear function consumes its argument exactly once, so NO duplicability side
  condition is needed and `⊸`-β is sound UNCONDITIONALLY via the linear cut
  `cderiv_substL`. Shares the term form `Term.app` with `impE`. -/
  | lolliE {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M (Prop'.lolli φ ψ)) (dN : CDeriv Γ₂ N φ)
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.app M N) ψ
  /-- `tensor-I` — multiplicative conjunction; the context JOINS, no shift. -/
  | tensorI {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M φ) (dN : CDeriv Γ₂ N ψ)
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.tensorIntro M N) (Prop'.tensor φ ψ)
  /-- `tensor-E` (`letTensor`) — THE case the current representation resists.
  Two LINEAR (`one`) binders extend the context by two, matching `shift`'s
  `letTensor` clause `cutoff + 2`; the context JOINS, no shift in the conclusion. -/
  | tensorE {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ χ : Prop'} {S B : Term}
      (dS : CDeriv Γ₁ S (Prop'.tensor φ ψ))
      (dB : CDeriv ((φ, Mult.one) :: (ψ, Mult.one) :: Γ₂) B χ)
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.letTensor S B) χ
  /-- `says-E` — affirmation elimination, migrated to `CJoin`. Binds ONE
  ADDITIVE (`many`) hypothesis `φ`; `shift`'s `saysBind` clause uses
  `cutoff + 1` on the body. The context JOINS, no shift in the conclusion. -/
  | saysE {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {p : Principal} {φ ψ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M (Prop'.says p φ))
      (dN : CDeriv ((φ, Mult.many) :: Γ₂) N ψ)
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.saysBind p M N) (Prop'.says p ψ)
  /-- `delegate` — chain composition, migrated to `CJoin`. No binder; both
  premises shift at the same cutoff (`shift`'s `delegate` clause). -/
  | delegate {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {p q : Principal} {φ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M (Prop'.says p (Prop'.speaksFor q p)))
      (dN : CDeriv Γ₂ N (Prop'.says q φ))
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.delegate M N) (Prop'.says (Principal.acting p q) φ)
  /-- `discharge` — `□_O φ` elimination, migrated to `CJoin`. No binder
  (`shift`'s `discharge` clause shifts both children at `cutoff`). -/
  | discharge {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {O : Obligation} {φ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M (Prop'.boxed O φ))
      (dN : CDeriv Γ₂ N (Prop'.atom 0))
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.discharge M N) φ
  /-- `says-extract` (`letSaysE`) — let-binder `says` elimination, migrated to
  `CJoin`. Binds ONE ADDITIVE (`many`) hypothesis; `shift`'s `letSays` clause
  uses `cutoff + 1` on the body. -/
  | letSaysE {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {p : Principal} {φ ψ : Prop'} {S B : Term}
      (dS : CDeriv Γ₁ S (Prop'.says p φ))
      (dB : CDeriv ((φ, Mult.many) :: Γ₂) B ψ)
      (hj : CJoin Γ₁ Γ₂ Γ) :
      CDeriv Γ (Term.letSays p S B) ψ

/-! ## `NoOne` kit — duplicability closed under the context surgeries.
These are needed early because the tightened `impE` carries a `NoOne` side
condition, so every lemma that RECONSTRUCTS an `impE` (weakening, substitution)
must re-establish `NoOne` of the argument's new context. -/

/-- The empty context is duplicable. -/
theorem noOne_nil : NoOne ([] : Carve.Ctx Prop') := by intro p hp; simp at hp

/-- `NoOne` on a cons splits into the head tag and the tail. -/
theorem noOne_cons {a : Prop'} {m : Mult} {Δ : Carve.Ctx Prop'} :
    NoOne ((a, m) :: Δ) ↔ m ≠ Mult.one ∧ NoOne Δ := by
  constructor
  · intro h
    exact ⟨h (a, m) List.mem_cons_self, fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact h1
    · exact h2 p hp'

/-- `NoOne` distributes over append. -/
theorem noOne_append {A B : Carve.Ctx Prop'} : NoOne (A ++ B) ↔ NoOne A ∧ NoOne B := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append.2 (Or.inl hp)),
           fun p hp => h p (List.mem_append.2 (Or.inr hp))⟩
  · rintro ⟨hA, hB⟩ p hp
    rcases List.mem_append.1 hp with h | h
    · exact hA p h
    · exact hB p h

/-- A `zeroed` block is duplicable — every tag is `zero`, hence `≠ one`. -/
theorem noOne_zeroed (Γ : Carve.Ctx Prop') : NoOne (zeroed Γ) := by
  intro p hp
  simp only [zeroed, List.mem_map] at hp
  obtain ⟨q, _, hq⟩ := hp
  subst hq
  show Mult.zero ≠ Mult.one
  decide

/-- **`NoOne` is closed under `CJoin` (merge direction).** Joining two
duplicable contexts yields a duplicable context: `MJoin m₁ m₂ m` with both
summands `≠ one` forces `m ≠ one` (the result of `zl`/`zr`/`mm` is a summand or
`many`). This is what re-establishes the argument's `NoOne` after a substitution
merges resources into it. -/
theorem noOne_cjoin_merge {A B C : Carve.Ctx Prop'} (hA : NoOne A) (hB : NoOne B)
    (h : CJoin A B C) : NoOne C := by
  induction h with
  | nil => exact noOne_nil
  | @cons a m₁ m₂ m A' B' C' hm _ ih =>
      obtain ⟨hm1, hA'⟩ := noOne_cons.1 hA
      obtain ⟨hm2, hB'⟩ := noOne_cons.1 hB
      refine noOne_cons.2 ⟨?_, ih hA' hB'⟩
      cases hm with
      | zl _ => exact hm2
      | zr _ => exact hm1
      | mm => decide

/-- Dropping the middle hypothesis of a `NoOne` context keeps it `NoOne` — used
by the substitution lemmas' `impE` case (the discharged hole vanishes from the
argument's context). -/
theorem noOne_drop_middle {A B : Carve.Ctx Prop'} {x : Prop' × Mult}
    (h : NoOne (A ++ x :: B)) : NoOne (A ++ B) := by
  rw [noOne_append] at h ⊢
  obtain ⟨a, m⟩ := x
  exact ⟨h.1, (noOne_cons.1 h.2).2⟩

/-- Every entry of a `zeroed` block carries the consumed tag `Mult.zero`. -/
theorem zeroed_getElem_zero (Γm : Carve.Ctx Prop') {k : Nat} {p : Prop' × Mult}
    (h : (zeroed Γm)[k]? = some p) : p.2 = Mult.zero := by
  unfold zeroed at h
  rw [List.getElem?_map] at h
  cases hq : Γm[k]? with
  | none => rw [hq] at h; simp at h
  | some q => rw [hq] at h; simp only [Option.map_some, Option.some.injEq] at h;
              rw [← h]

/-- **Insert-preservation for the leftover side condition.** Inserting a
`zeroed Γm` block at position `Γl.length` preserves `AllZeroExcept`: the block
is all-`zero` (trivially unused), and the surrounding `Γl`/`Γr` positions map
from the original by the same append arithmetic as the index shift. The
demanded index moves exactly as `shift` moves the `var`. This is what lets the
var case of `cderiv_shift` re-derive the side condition after weakening. -/
theorem allZeroExcept_insert {Γl Γm Γr : Carve.Ctx Prop'} {i : Nat}
    (hz : AllZeroExcept (Γl ++ Γr) i) :
    AllZeroExcept (Γl ++ zeroed Γm ++ Γr)
      (if i < Γl.length then i else i + Γm.length) := by
  intro j p hj hget
  by_cases hjL : j < Γl.length
  · -- `j` lands in `Γl`; its tag is inherited from the original context.
    rw [List.getElem?_append_left (by simp [zeroed_length]; omega),
        List.getElem?_append_left hjL] at hget
    have horig : (Γl ++ Γr)[j]? = some p := by
      rw [List.getElem?_append_left hjL]; exact hget
    have hne : j ≠ i := by
      by_cases hi : i < Γl.length
      · rw [if_pos hi] at hj; exact hj
      · omega
    exact hz j p hne horig
  · by_cases hjZ : j < Γl.length + Γm.length
    · -- `j` lands in the inserted `zeroed Γm` block: tag is `zero` outright.
      rw [List.getElem?_append_left (by simp [zeroed_length]; omega),
          List.getElem?_append_right (by omega)] at hget
      exact zeroed_getElem_zero Γm hget
    · -- `j` lands in `Γr`; its tag is inherited from the original at `j - |Γm|`.
      rw [List.getElem?_append_right (by simp [zeroed_length]; omega)] at hget
      have horig : (Γl ++ Γr)[j - Γm.length]? = some p := by
        rw [List.getElem?_append_right (by omega),
            show (j - Γm.length) - Γl.length
                = j - (Γl ++ zeroed Γm).length from by simp [zeroed_length]; omega]
        exact hget
      have hne : j - Γm.length ≠ i := by
        by_cases hi : i < Γl.length
        · omega
        · rw [if_neg hi] at hj; omega
      exact hz (j - Γm.length) p hne horig

/-- **The keystone (L3-shaped): weakening-in-the-middle over the real judgment.**
Inserting a `zero`-tagged (present-but-unused) block `zeroed Γm` at position
`Γl.length` shifts the subject's free variables past that point. Mirrors
`CarveProto.d_shift` on the real `Term`/`Prop'`: the `tensorE` case closes with
the IH taken on the two-binder-extended context and cutoff `|Γl| + 2` matching
`shift`'s `letTensor` clause; `cjoin_split`/`cjoin_insert` move no index, and no
shift-commutation lemma is needed. This is the structural fact the current
`{additive, linear}` representation cannot prove for `tensorE`. -/
noncomputable def cderiv_shift {Γfull : Carve.Ctx Prop'} {M : Term} {A : Prop'}
    (d : CDeriv Γfull M A) :
    ∀ (Γl Γm Γr : Carve.Ctx Prop'), Γfull = Γl ++ Γr →
      CDeriv (Γl ++ zeroed Γm ++ Γr) (shift M Γm.length Γl.length) A := by
  induction d with
  | @var Γ i φ m h hm hz =>
      intro Γl Γm Γr hΓ
      subst hΓ
      simp only [shift]
      by_cases hcut : i < Γl.length
      · rw [if_pos hcut]
        refine CDeriv.var (m := m) ?_ hm ?_
        · rw [List.getElem?_append_left (by simp [zeroed_length]; omega),
              List.getElem?_append_left hcut]
          rwa [List.getElem?_append_left hcut] at h
        · have hz' := allZeroExcept_insert (Γm := Γm) hz
          rwa [if_pos hcut] at hz'
      · rw [if_neg hcut]
        refine CDeriv.var (m := m) ?_ hm ?_
        · rw [List.getElem?_append_right (by simp [zeroed_length]; omega),
              show i + Γm.length - (Γl ++ zeroed Γm).length = i - Γl.length from by
                simp [zeroed_length]; omega]
          rwa [List.getElem?_append_right (by omega)] at h
        · have hz' := allZeroExcept_insert (Γm := Γm) hz
          rwa [if_neg hcut] at hz'
  | impI _d ih =>
      intro Γl Γm Γr hΓ
      subst hΓ
      simp only [shift]
      exact CDeriv.impI (by simpa using ih (_ :: Γl) Γm Γr rfl)
  | @impE Γ Γ₁ Γ₂ φ ψ M N _dM _dN hj hdup ihM ihN =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      obtain ⟨hL, hR⟩ := noOne_append.1 hdup
      exact CDeriv.impE (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl)
                        (by rw [← hn2]; exact ihN Γl₂ Γm Γr₂ rfl)
                        (cjoin_insert hjl hjr)
                        (noOne_append.2 ⟨noOne_append.2 ⟨hL, noOne_zeroed Γm⟩, hR⟩)
  | lolliI _d ih =>
      intro Γl Γm Γr hΓ
      subst hΓ
      simp only [shift]
      exact CDeriv.lolliI (by simpa using ih (_ :: Γl) Γm Γr rfl)
  | lolliE _dM _dN hj ihM ihN =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact CDeriv.lolliE (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl)
                          (by rw [← hn2]; exact ihN Γl₂ Γm Γr₂ rfl)
                          (cjoin_insert hjl hjr)
  | tensorI _dM _dN hj ihM ihN =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact CDeriv.tensorI (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl)
                           (by rw [← hn2]; exact ihN Γl₂ Γm Γr₂ rfl)
                           (cjoin_insert hjl hjr)
  | tensorE _dS _dB hj ihS ihB =>
      -- THE case the current `{additive, linear}` representation resists.
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      refine CDeriv.tensorE (by rw [← hn1]; exact ihS Γl₁ Γm Γr₁ rfl) ?_
        (cjoin_insert hjl hjr)
      -- Two LINEAR binders extend the context by two; body cutoff |Γl| + 2
      -- matches `shift`'s `letTensor` clause on the nose.
      have h := ihB (_ :: _ :: Γl₂) Γm Γr₂ rfl
      simpa [hn2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  | saysE _dM _dN hj ihM ihN =>
      -- One ADDITIVE binder on the body → IH on `_ :: Γl₂`, cutoff `|Γl| + 1`
      -- matching `shift`'s `saysBind` clause; the two premises `cjoin_split`.
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      refine CDeriv.saysE (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl) ?_
        (cjoin_insert hjl hjr)
      have h := ihN (_ :: Γl₂) Γm Γr₂ rfl
      simpa [hn2] using h
  | delegate _dM _dN hj ihM ihN =>
      -- No binder; both premises shift at `|Γl|`, exactly the `impE` pattern.
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact CDeriv.delegate (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl)
                            (by rw [← hn2]; exact ihN Γl₂ Γm Γr₂ rfl)
                            (cjoin_insert hjl hjr)
  | discharge _dM _dN hj ihM ihN =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact CDeriv.discharge (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl)
                             (by rw [← hn2]; exact ihN Γl₂ Γm Γr₂ rfl)
                             (cjoin_insert hjl hjr)
  | letSaysE _dS _dB hj ihS ihB =>
      -- One ADDITIVE binder on the body → cutoff `|Γl| + 1` matching `shift`'s
      -- `letSays` clause; same shape as `saysE`.
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      refine CDeriv.letSaysE (by rw [← hn1]; exact ihS Γl₁ Γm Γr₁ rfl) ?_
        (cjoin_insert hjl hjr)
      have h := ihB (_ :: Γl₂) Γm Γr₂ rfl
      simpa [hn2] using h

/-! ## Increment 3a — ADDITIVE (`many`) substitution preservation over `CDeriv`.

Substituting a term `N` for an ADDITIVE (`Mult.many`) hypothesis at position
`Γl.length` preserves `CDeriv`. This is the L3 (additive) half of the CARVe
substitution property — the QTT/leftover analogue of `PropDeriv`'s
`propDeriv_substAt` (`DLC.Decidability`), mirrored onto the resource-vector
context. Because the discharged hypothesis is `many` (unrestricted), the
replacement `N` must itself consume NO linear resources: it is typed under the
all-`zero` context `zeroed Γr` (Wood–Atkey's usage-context substitution needs
weakening only by 0-use-variable introduction, which `cderiv_shift` supplies;
an unrestricted variable may be duplicated 0+ times, so its filler must be
resource-free). See the module footer for the exact scope and the deferred
linear (L4) case.

The support lemmas below are the "kit" the induction needs (all machine-checked
here, no `sorry`). -/

/-- `zeroed` distributes over `cons`. -/
theorem zeroed_cons {α : Type} (a : α) (mm : Mult) (Γ : Carve.Ctx α) :
    zeroed ((a, mm) :: Γ) = (a, Mult.zero) :: zeroed Γ := by simp [zeroed]

/-- An all-`zero` context is literally its own `zeroed` image. -/
theorem ctx_all_zero_eq_zeroed (Γ : Carve.Ctx Prop') :
    (∀ (j : Nat) (p : Prop' × Mult), Γ[j]? = some p → p.2 = Mult.zero) → Γ = zeroed Γ := by
  induction Γ with
  | nil => intro _; rfl
  | cons a tl ih =>
      intro h
      obtain ⟨a1, a2⟩ := a
      have h0 : a2 = Mult.zero := h 0 (a1, a2) rfl
      have htl : tl = zeroed tl := ih (fun k p hk => h (k + 1) p (by simpa using hk))
      subst h0
      rw [zeroed_cons, ← htl]

/-- **At a `many`-substitution hit, the surrounding context is all-`zero`.**
`AllZeroExcept` at the hole position forces both `Γl` and `Γr` to equal their
`zeroed` images — exactly what lets `cderiv_shift` land `N` (typed under
`zeroed Γr`) into `Γl ++ Γr` at the leaf. -/
theorem allZeroExcept_split_zeroed {Γl Γr : Carve.Ctx Prop'} {φ : Prop'} {m : Mult}
    (hz : AllZeroExcept (Γl ++ (φ, m) :: Γr) Γl.length) :
    Γl = zeroed Γl ∧ Γr = zeroed Γr := by
  refine ⟨ctx_all_zero_eq_zeroed Γl ?_, ctx_all_zero_eq_zeroed Γr ?_⟩
  · intro j p hj
    have hlt : j < Γl.length := by
      rcases Nat.lt_or_ge j Γl.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj; exact absurd hj (by simp)
    have hidx : (Γl ++ (φ, m) :: Γr)[j]? = some p := by
      rw [List.getElem?_append_left hlt]; exact hj
    exact hz j p (by omega) hidx
  · intro k p hk
    have hidx : (Γl ++ (φ, m) :: Γr)[Γl.length + (k + 1)]? = some p := by
      rw [List.getElem?_append_right (by omega),
          show Γl.length + (k + 1) - Γl.length = k + 1 from by omega,
          List.getElem?_cons_succ]
      exact hk
    exact hz (Γl.length + (k + 1)) p (by omega) hidx

/-- **Removing the substituted position preserves the leftover condition.**
Dropping the `(φ, m)` hole at `Γl.length` maps `AllZeroExcept … i` to
`AllZeroExcept (Γl ++ Γr)` at the down-shifted index — the mirror of
`allZeroExcept_insert`, used by the `var` case's non-hit branch. -/
theorem allZeroExcept_remove {Γl Γr : Carve.Ctx Prop'} {φ : Prop'} {m : Mult} {i : Nat}
    (hz : AllZeroExcept (Γl ++ (φ, m) :: Γr) i) (_hi : i ≠ Γl.length) :
    AllZeroExcept (Γl ++ Γr) (if i < Γl.length then i else i - 1) := by
  intro j p hj hget
  by_cases hjL : j < Γl.length
  · rw [List.getElem?_append_left hjL] at hget
    have hold : (Γl ++ (φ, m) :: Γr)[j]? = some p := by
      rw [List.getElem?_append_left hjL]; exact hget
    have hne : j ≠ i := by
      by_cases hiL : i < Γl.length
      · rw [if_pos hiL] at hj; exact hj
      · omega
    exact hz j p hne hold
  · have hjge : Γl.length ≤ j := by omega
    rw [List.getElem?_append_right hjge] at hget
    have hold : (Γl ++ (φ, m) :: Γr)[j + 1]? = some p := by
      rw [List.getElem?_append_right (by omega),
          show j + 1 - Γl.length = (j - Γl.length) + 1 from by omega,
          List.getElem?_cons_succ]
      exact hget
    have hne : j + 1 ≠ i := by
      by_cases hiL : i < Γl.length
      · omega
      · rw [if_neg hiL] at hj; omega
    exact hz (j + 1) p hne hold

/-- A `CJoin` shares its entries' propositions with its left operand, so their
`zeroed` images coincide. -/
theorem cjoin_zeroed_left {α : Type} {Γ₁ Γ₂ Γ : Carve.Ctx α} (h : CJoin Γ₁ Γ₂ Γ) :
    zeroed Γ₁ = zeroed Γ := by
  induction h with
  | nil => rfl
  | @cons a mm1 mm2 mm Δ1 Δ2 Δ _ _ ih => rw [zeroed_cons, zeroed_cons, ih]

/-- …and with its right operand. -/
theorem cjoin_zeroed_right {α : Type} {Γ₁ Γ₂ Γ : Carve.Ctx α} (h : CJoin Γ₁ Γ₂ Γ) :
    zeroed Γ₂ = zeroed Γ := by
  induction h with
  | nil => rfl
  | @cons a mm1 mm2 mm Δ1 Δ2 Δ _ _ ih => rw [zeroed_cons, zeroed_cons, ih]

/-- Append two joins (the `Γm := []` degenerate of `cjoin_insert`): reassembles
the result context after the substituted middle position has been dropped. -/
noncomputable def cjoin_append {α : Type} {A₁ A₂ A B₁ B₂ B : Carve.Ctx α}
    (h1 : CJoin A₁ A₂ A) (h2 : CJoin B₁ B₂ B) :
    CJoin (A₁ ++ B₁) (A₂ ++ B₂) (A ++ B) := by
  induction h1 with
  | nil => simpa using h2
  | cons hm _ ih => exact CJoin.cons hm ih

/-- The split of a join at a `(φ, m)` hole: the elementwise `MJoin m₁ m₂ m` at
the hole plus the left/right joins around it, with named tails. -/
structure SplitAtCons (Γ₁ Γ₂ Γl Γr : Carve.Ctx Prop') (φ : Prop') (m : Mult) : Type where
  Γl₁ : Carve.Ctx Prop'
  Γr₁ : Carve.Ctx Prop'
  Γl₂ : Carve.Ctx Prop'
  Γr₂ : Carve.Ctx Prop'
  m₁ : Mult
  m₂ : Mult
  e₁ : Γ₁ = Γl₁ ++ (φ, m₁) :: Γr₁
  e₂ : Γ₂ = Γl₂ ++ (φ, m₂) :: Γr₂
  n₁ : Γl₁.length = Γl.length
  n₂ : Γl₂.length = Γl.length
  hmj : MJoin m₁ m₂ m
  jl : CJoin Γl₁ Γl₂ Γl
  jr : CJoin Γr₁ Γr₂ Γr

/-- Split `CJoin Γ₁ Γ₂ (Γl ++ (φ, m) :: Γr)` at the hole. -/
noncomputable def cjoin_split_cons {Γ₁ Γ₂ Γl Γr : Carve.Ctx Prop'} {φ : Prop'} {m : Mult}
    (h : CJoin Γ₁ Γ₂ (Γl ++ (φ, m) :: Γr)) : SplitAtCons Γ₁ Γ₂ Γl Γr φ m := by
  obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, e1, e2, n1, n2, jl, jr⟩ := cjoin_split Γl ((φ, m) :: Γr) h
  cases jr with
  | cons hmj jrtail =>
      exact ⟨Γl₁, _, Γl₂, _, _, _, e1, e2, n1, n2, hmj, jl, jrtail⟩

/-- The hole tag cannot be `one`: an `MJoin` into a non-`one` result has only
non-`one` operands (needed to keep the IH applicable through each premise). -/
theorem mjoin_ne_one {m₁ m₂ m : Mult} (h : MJoin m₁ m₂ m) (hm : m ≠ Mult.one) :
    m₁ ≠ Mult.one ∧ m₂ ≠ Mult.one := by
  cases h with
  | zl _ => exact ⟨by decide, hm⟩
  | zr _ => exact ⟨hm, by decide⟩
  | mm => exact ⟨by decide, by decide⟩

/-- **Additive substitution preservation (auxiliary, all nine constructors).**
`φ`/`N` are fixed; the hole tag is generalised to any `m ≠ one` (i.e.
`m ∈ {zero, many}`) so the induction can recurse through each `CJoin` premise,
whose hole tag may be `zero` (routed away) or `many` (the used side). -/
private noncomputable def cderiv_substA_aux {Γfull : Carve.Ctx Prop'} {M : Term} {ψ : Prop'}
    (φ : Prop') (N : Term) (dM : CDeriv Γfull M ψ) :
    ∀ (Γl Γr : Carve.Ctx Prop') (m : Mult), Γfull = Γl ++ (φ, m) :: Γr → m ≠ Mult.one →
      CDeriv (zeroed Γr) N φ → CDeriv (Γl ++ Γr) (substAt M N Γl.length) ψ := by
  induction dM with
  | @var Γ i χ mvar h hmvar hz =>
      intro Γl Γr m hΓ _ dN
      subst hΓ
      unfold substAt
      by_cases heq : i = Γl.length
      · -- HIT: place the shifted `N`; the surroundings are all-`zero`.
        rw [if_pos heq]
        subst heq
        have hval : φ = χ ∧ m = mvar := by
          have hh := h
          rw [List.getElem?_append_right (le_refl Γl.length)] at hh
          simpa using hh
        obtain ⟨hφχ, _⟩ := hval
        subst hφχ
        obtain ⟨hzl, hzr⟩ := allZeroExcept_split_zeroed hz
        have hshift := cderiv_shift dN [] Γl (zeroed Γr) (by simp)
        simp only [List.nil_append, List.length_nil] at hshift
        rw [← hzl, ← hzr] at hshift
        exact hshift
      · rw [if_neg heq]
        by_cases hgt : i > Γl.length
        · rw [if_pos hgt]
          refine CDeriv.var (m := mvar) ?_ hmvar ?_
          · have hge : Γl.length ≤ i := Nat.le_of_lt hgt
            rw [List.getElem?_append_right hge] at h
            rw [show i - Γl.length = (i - Γl.length - 1) + 1 from by omega,
                List.getElem?_cons_succ] at h
            rw [List.getElem?_append_right (show Γl.length ≤ i - 1 from by omega),
                show i - 1 - Γl.length = i - Γl.length - 1 from by omega]
            exact h
          · have hz' := allZeroExcept_remove hz heq
            rwa [if_neg (by omega)] at hz'
        · rw [if_neg hgt]
          have hlt : i < Γl.length := by omega
          refine CDeriv.var (m := mvar) ?_ hmvar ?_
          · rw [List.getElem?_append_left hlt]
            rwa [List.getElem?_append_left hlt] at h
          · have hz' := allZeroExcept_remove hz heq
            rwa [if_pos hlt] at hz'
  | @impI Γ φb ψb Mb _ ih =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      unfold substAt
      have hP := ih ((φb, Mult.many) :: Γl) Γr m rfl hm dN
      exact CDeriv.impI (by simpa using hP)
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne _ _ hj hdup ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      have hN := ihN Γl₂ Γr₂ m₂ rfl hm2 (by rw [cjoin_zeroed_right hjr]; exact dN)
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.impE hM hN (cjoin_append hjl hjr) (noOne_drop_middle hdup)
  | @lolliI Γ φb ψb Mb _ ih =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      unfold substAt
      have hP := ih ((φb, Mult.one) :: Γl) Γr m rfl hm dN
      exact CDeriv.lolliI (by simpa using hP)
  | @lolliE Γ Γ₁ Γ₂ φe ψe Me Ne _ _ hj ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      have hN := ihN Γl₂ Γr₂ m₂ rfl hm2 (by rw [cjoin_zeroed_right hjr]; exact dN)
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.lolliE hM hN (cjoin_append hjl hjr)
  | @tensorI Γ Γ₁ Γ₂ φt ψt Mt Nt _ _ hj ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      have hN := ihN Γl₂ Γr₂ m₂ rfl hm2 (by rw [cjoin_zeroed_right hjr]; exact dN)
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.tensorI hM hN (cjoin_append hjl hjr)
  | @tensorE Γ Γ₁ Γ₂ φt ψt χt St Bt _ _ hj ihS ihB =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hS := ihS Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      rw [hn1] at hS
      have hB := ihB ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ m₂ rfl hm2
        (by rw [cjoin_zeroed_right hjr]; exact dN)
      refine CDeriv.tensorE hS ?_ (cjoin_append hjl hjr)
      simpa [hn2] using hB
  | @saysE Γ Γ₁ Γ₂ p φs ψs Ms Nb _ _ hj ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      rw [hn1] at hM
      have hN := ihN ((φs, Mult.many) :: Γl₂) Γr₂ m₂ rfl hm2
        (by rw [cjoin_zeroed_right hjr]; exact dN)
      refine CDeriv.saysE hM ?_ (cjoin_append hjl hjr)
      simpa [hn2] using hN
  | @delegate Γ Γ₁ Γ₂ p q φd Md Nd _ _ hj ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      have hN := ihN Γl₂ Γr₂ m₂ rfl hm2 (by rw [cjoin_zeroed_right hjr]; exact dN)
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.delegate hM hN (cjoin_append hjl hjr)
  | @discharge Γ Γ₁ Γ₂ O φd Md Nd _ _ hj ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      have hN := ihN Γl₂ Γr₂ m₂ rfl hm2 (by rw [cjoin_zeroed_right hjr]; exact dN)
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.discharge hM hN (cjoin_append hjl hjr)
  | @letSaysE Γ Γ₁ Γ₂ p φs ψs St Bt _ _ hj ihS ihB =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hS := ihS Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      rw [hn1] at hS
      have hB := ihB ((φs, Mult.many) :: Γl₂) Γr₂ m₂ rfl hm2
        (by rw [cjoin_zeroed_right hjr]; exact dN)
      refine CDeriv.letSaysE hS ?_ (cjoin_append hjl hjr)
      simpa [hn2] using hB

/-- **Additive (L3) substitution preservation over `CDeriv`.** Substituting a
`N : φ` (typed with NO linear resources, under `zeroed Γr`) for the ADDITIVE
(`Mult.many`) hypothesis at position `Γl.length` preserves the CARVe judgment,
dropping that position. Proved for ALL nine constructors. The mirror of
`propDeriv_substAt` (`DLC.Decidability`) over the resource-vector context. -/
noncomputable def cderiv_substA {Γl Γr : Carve.Ctx Prop'} {φ ψ : Prop'} {M N : Term}
    (dM : CDeriv (Γl ++ (φ, Mult.many) :: Γr) M ψ)
    (dN : CDeriv (zeroed Γr) N φ) :
    CDeriv (Γl ++ Γr) (substAt M N Γl.length) ψ :=
  cderiv_substA_aux φ N dM Γl Γr Mult.many rfl (by decide) dN

/-! ## Increment 3b — LINEAR (`one`) substitution preservation over `CDeriv`.

Substituting `N : φ` — carrying its OWN resources `Δ` — for the LINEAR
(`Mult.one`) hypothesis at position `Γl.length`. Unlike the additive case, `N`'s
context does NOT vanish: it is `CJoin`-MERGED into the leftover of `M` at the
positions after the hole (`CJoin Γr Δ Γr'`, usage-vector addition — the
linear-algebra step of Wood–Atkey, arXiv:2005.02247). This is the CUT rule: a
`one` hypothesis routes to exactly ONE `CJoin` branch (`mjoin_one_not_shared`),
so the induction splits on which premise consumed it; the OTHER branch carries
the hole at tag `zero` and simply drops it (`cderiv_dropZero_aux`). The de Bruijn
discipline of `substAt`/`shift` (lift `N` by `Γl.length`) makes `N`'s variables
land exactly on the `Γr` positions — so `Δ` shares its propositions with `Γr`
(enforced by `CJoin Γr Δ Γr'`) and never reaches `Γl`. The reassembly of the two
premises' leftovers with `Δ` is a partial-commutative-monoid REASSOCIATION
(`cjoin_reassoc`), the substructural counterpart of `A ⊕ (B ⊕ D) = (A ⊕ B) ⊕ D`.

Prior art (web-searched 2026-07-22):
- Wood & Atkey, *A Linear Algebra Approach to Linear Metatheory* (arXiv:2005.02247):
  substitution as a usage-respecting environment/kit; linear systems do NOT
  validate naive substitution (context-union-under-binder fails), the
  environment method (usage = semiring vector, split = semiring `+`) is the fix.
  https://arxiv.org/abs/2005.02247
- Wood & Atkey, *A Framework for Substructural Type Systems* (ESOP 2022):
  https://bentnib.org/quant-framework.pdf
- Zalakain & Dardha, *π with Leftovers* (FORTE 2021): simultaneous
  renaming/substitution over a general usage algebra; leftover output contexts
  are exactly this `Γr'`. https://arxiv.org/pdf/2005.05902 -/

/-- Every entry of a `zeroed` block, read at a `CJoin`, is `zero` — the
all-`zero` predicate the hit case feeds to `cjoin_left_all_zero`. -/
theorem mjoin_zero {m₁ m₂ : Mult} (h : MJoin m₁ m₂ Mult.zero) :
    m₁ = Mult.zero ∧ m₂ = Mult.zero := by
  cases h with
  | zl => exact ⟨rfl, rfl⟩
  | zr => exact ⟨rfl, rfl⟩

/-- A `one` result with a `one` LEFT summand forces the right summand `zero`
(`MJoin one m₂ one` has only the `zr` shape). -/
theorem mjoin_one_left {m₂ : Mult} (h : MJoin Mult.one m₂ Mult.one) : m₂ = Mult.zero := by
  cases h; rfl

/-- **A `one` routes to exactly one branch.** If the left summand is NOT `one`,
then it is `zero` and the right summand carries the whole `one` — the algebraic
content of `mjoin_one_not_shared`. Split on the tag DATA (not by `cases` on the
`MJoin`, which cannot eliminate into the `Type`-valued derivation) so the linear
hole lands entirely on one premise. -/
theorem mjoin_one_notleft {m₁ m₂ : Mult} (h : MJoin m₁ m₂ Mult.one)
    (hne : m₁ ≠ Mult.one) : m₁ = Mult.zero ∧ m₂ = Mult.one := by
  cases h with
  | zl => exact ⟨rfl, rfl⟩
  | zr => exact absurd rfl hne

/-- `MJoin` is commutative. -/
theorem mjoin_comm {a b c : Mult} (h : MJoin a b c) : MJoin b a c := by
  cases h
  · exact MJoin.zr _
  · exact MJoin.zl _
  · exact MJoin.mm

/-- `CJoin` is commutative (elementwise `mjoin_comm`). -/
noncomputable def cjoin_comm {α : Type} {A B C : Carve.Ctx α} (h : CJoin A B C) :
    CJoin B A C := by
  induction h with
  | nil => exact CJoin.nil
  | cons hm _ ih => exact CJoin.cons (mjoin_comm hm) ih

/-- **Joining an all-`zero` left operand is the identity.** If every tag of `A`
is `zero`, then `A ⊕ Δ = Δ` on the nose. At the `one`-hit, `AllZeroExcept`
forces the leftover `Γr` all-`zero`, so the merged context `Γr'` equals `N`'s
own context `Δ` — `N` brings ALL the resources at the hole. -/
theorem cjoin_left_all_zero {α : Type} {A Δ E : Carve.Ctx α}
    (h : CJoin A Δ E) (hz : A = zeroed A) : E = Δ := by
  induction h with
  | nil => rfl
  | @cons a m₁ m₂ m A' Δ' E' hm _ ih =>
      rw [zeroed_cons] at hz
      injection hz with hhd htl
      injection hhd with _ hm1
      subst hm1
      have hE : E' = Δ' := ih htl
      subst hE
      cases hm with
      | zl => rfl
      | zr => rfl

/-- The resource-monoid SUM, used as the reassociation WITNESS tag. Total by
convention; the genuinely-undefined joins (`one ⊕ one`, `one ⊕ many`) are
never reached — `cjoin_reassoc`'s premises rule them out (the `MJoin` case
analysis has no constructor for them). -/
def madd : Mult → Mult → Mult
  | Mult.zero, d => d
  | Mult.one,  _ => Mult.one
  | Mult.many, _ => Mult.many

/-- **`MJoin` reassociation.** From `a ⊕ b = ab` and `ab ⊕ d = e`, the witness
`madd a d` satisfies `a ⊕ d = madd a d` and `(madd a d) ⊕ b = e`. This is
associativity+commutativity of the partial commutative monoid `{zero,one,many}`
— the elementwise heart of the linear-algebra substitution step. -/
theorem mjoin_reassoc {a b ab d e : Mult} (h1 : MJoin a b ab) (h2 : MJoin ab d e) :
    MJoin a d (madd a d) ∧ MJoin (madd a d) b e := by
  cases a <;> cases d <;> simp only [madd] <;> cases h1 <;> cases h2 <;>
    refine ⟨?_, ?_⟩ <;>
    first
      | exact MJoin.zl _
      | exact MJoin.zr _
      | exact MJoin.mm

/-- The reassociation result at the context level: the merged middle `AD` plus
the two `CJoin`s that rebuild `E` through it. -/
structure CReassoc {α : Type} (A B D E : Carve.Ctx α) : Type where
  AD : Carve.Ctx α
  hAD : CJoin A D AD
  hADB : CJoin AD B E

/-- **`CJoin` reassociation** (elementwise `mjoin_reassoc`). From `A ⊕ B = AB`
and `AB ⊕ D = E`, produce `AD = A ⊕ D` with `AD ⊕ B = E`. This reroutes `N`'s
resources `D` past one premise's leftover `B` — the substructural
`A ⊕ (B ⊕ D) = (A ⊕ B) ⊕ D` that lets the cut merge `Δ` into the surviving
premise while the consumed premise is dropped. -/
noncomputable def cjoin_reassoc {α : Type} {A B AB D E : Carve.Ctx α}
    (h1 : CJoin A B AB) : CJoin AB D E → CReassoc A B D E := by
  induction h1 generalizing D E with
  | nil => intro h2; cases h2; exact ⟨[], CJoin.nil, CJoin.nil⟩
  | @cons a a1 b1 ab1 A' B' AB' hm _ ih =>
      intro h2
      cases h2 with
      | @cons _ _ d1 _ _ D' _ hm2 hrest2 =>
          obtain ⟨mrl, mrr⟩ := mjoin_reassoc hm hm2
          exact ⟨(a, madd a1 d1) :: (ih hrest2).AD,
                 CJoin.cons mrl (ih hrest2).hAD,
                 CJoin.cons mrr (ih hrest2).hADB⟩

/-- **Strengthening: drop an unused (`zero`-tagged) hypothesis.** A `zero` hole
at position `Γl.length` is never referenced by any `var` leaf (a leaf demands a
non-`zero` tag at its own position, and a `zero` result forces every summand
`zero`), so `substAt M N Γl.length` never PLACES `N` — it only re-indexes past
the dropped slot. `N` is carried untouched purely to match the syntactic form
used by the linear cut's discarded branch. Proved for all nine constructors. -/
private noncomputable def cderiv_dropZero_aux {Γfull : Carve.Ctx Prop'} {M : Term}
    {ψ : Prop'} (φ : Prop') (N : Term) (dM : CDeriv Γfull M ψ) :
    ∀ (Γl Γr : Carve.Ctx Prop'), Γfull = Γl ++ (φ, Mult.zero) :: Γr →
      CDeriv (Γl ++ Γr) (substAt M N Γl.length) ψ := by
  induction dM with
  | @var Γ i χ mvar h hmvar hz =>
      intro Γl Γr hΓ
      subst hΓ
      unfold substAt
      by_cases heq : i = Γl.length
      · exfalso; subst heq
        rw [List.getElem?_append_right (le_refl Γl.length)] at h
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at h
        exact hmvar h.2.symm
      · rw [if_neg heq]
        by_cases hgt : i > Γl.length
        · rw [if_pos hgt]
          refine CDeriv.var (m := mvar) ?_ hmvar ?_
          · have hge : Γl.length ≤ i := Nat.le_of_lt hgt
            rw [List.getElem?_append_right hge] at h
            rw [show i - Γl.length = (i - Γl.length - 1) + 1 from by omega,
                List.getElem?_cons_succ] at h
            rw [List.getElem?_append_right (show Γl.length ≤ i - 1 from by omega),
                show i - 1 - Γl.length = i - Γl.length - 1 from by omega]
            exact h
          · have hz' := allZeroExcept_remove hz heq
            rwa [if_neg (by omega)] at hz'
        · rw [if_neg hgt]
          have hlt : i < Γl.length := by omega
          refine CDeriv.var (m := mvar) ?_ hmvar ?_
          · rw [List.getElem?_append_left hlt]
            rwa [List.getElem?_append_left hlt] at h
          · have hz' := allZeroExcept_remove hz heq
            rwa [if_pos hlt] at hz'
  | @impI Γ φb ψb Mb _ ih =>
      intro Γl Γr hΓ; subst hΓ; unfold substAt
      exact CDeriv.impI (by simpa using ih ((φb, Mult.many) :: Γl) Γr rfl)
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne _ _ hj hdup ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; have hN := ihN Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.impE hM hN (cjoin_append hjl hjr) (noOne_drop_middle hdup)
  | @lolliI Γ φb ψb Mb _ ih =>
      intro Γl Γr hΓ; subst hΓ; unfold substAt
      exact CDeriv.lolliI (by simpa using ih ((φb, Mult.one) :: Γl) Γr rfl)
  | @lolliE Γ Γ₁ Γ₂ φe ψe Me Ne _ _ hj ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; have hN := ihN Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.lolliE hM hN (cjoin_append hjl hjr)
  | @tensorI Γ Γ₁ Γ₂ φt ψt Mt Nt _ _ hj ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; have hN := ihN Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.tensorI hM hN (cjoin_append hjl hjr)
  | @tensorE Γ Γ₁ Γ₂ φt ψt χt St Bt _ _ hj ihS ihB =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hS := ihS Γl₁ Γr₁ rfl; rw [hn1] at hS
      have hB := ihB ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ rfl
      refine CDeriv.tensorE hS ?_ (cjoin_append hjl hjr)
      simpa [hn2] using hB
  | @saysE Γ Γ₁ Γ₂ p φs ψs Ms Nb _ _ hj ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; rw [hn1] at hM
      have hN := ihN ((φs, Mult.many) :: Γl₂) Γr₂ rfl
      refine CDeriv.saysE hM ?_ (cjoin_append hjl hjr)
      simpa [hn2] using hN
  | @delegate Γ Γ₁ Γ₂ p q φd Md Nd _ _ hj ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; have hN := ihN Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.delegate hM hN (cjoin_append hjl hjr)
  | @discharge Γ Γ₁ Γ₂ O φd Md Nd _ _ hj ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; have hN := ihN Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.discharge hM hN (cjoin_append hjl hjr)
  | @letSaysE Γ Γ₁ Γ₂ p φs ψs St Bt _ _ hj ihS ihB =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hS := ihS Γl₁ Γr₁ rfl; rw [hn1] at hS
      have hB := ihB ((φs, Mult.many) :: Γl₂) Γr₂ rfl
      refine CDeriv.letSaysE hS ?_ (cjoin_append hjl hjr)
      simpa [hn2] using hB

/-- **Linear (L4) substitution preservation (auxiliary, all nine constructors).**
`φ`/`N` are fixed; the hole tag is `Mult.one`. At the single `var` leaf that
consumes it the hole MUST be hit (a `one` at any OTHER position violates
`AllZeroExcept`), where `N` (typed under its own `Δ`) is placed via
`cderiv_shift` and — because `AllZeroExcept` forces the leftover `Γr`
all-`zero` — the merged context `Γr'` collapses to exactly `Δ`
(`cjoin_left_all_zero`). At every `CJoin` premise the `one` routes to exactly
one branch (`MJoin _ _ one` has only `zl`/`zr`, never `mm`): that branch
recurses here with `Δ` re-routed past the sibling's leftover
(`cjoin_reassoc`); the sibling carries the hole at `zero` and is discharged by
`cderiv_dropZero_aux`. -/
private noncomputable def cderiv_substL_aux {Γfull : Carve.Ctx Prop'} {M : Term}
    {ψ : Prop'} (φ : Prop') (N : Term) (dM : CDeriv Γfull M ψ) :
    ∀ (Γl Γr Δ Γr' : Carve.Ctx Prop'), Γfull = Γl ++ (φ, Mult.one) :: Γr →
      CDeriv Δ N φ → CJoin Γr Δ Γr' →
      CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ := by
  induction dM with
  | @var Γ i χ mvar h hmvar hz =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      unfold substAt
      -- The `one` hole forces this leaf to hit it.
      have heq : i = Γl.length := by
        by_contra hne
        have hzero := hz Γl.length (φ, Mult.one) (fun he => hne he.symm)
          (by rw [List.getElem?_append_right (le_refl Γl.length)]; simp)
        simp at hzero
      rw [if_pos heq]
      rw [heq] at h hz
      obtain ⟨hzl, hzr⟩ := allZeroExcept_split_zeroed hz
      -- `χ = φ` from the hit lookup.
      rw [List.getElem?_append_right (le_refl Γl.length)] at h
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hφχ, _⟩ := h
      subst hφχ
      -- Leftover `Γr` all-`zero` ⟹ the merge `Γr'` is exactly `Δ`.
      have heE : Γr' = Δ := cjoin_left_all_zero hc hzr
      subst Γr'
      have hshift := cderiv_shift dN [] Γl Δ (by simp)
      simp only [List.nil_append, List.length_nil] at hshift
      rwa [← hzl] at hshift
  | @impI Γ φb ψb Mb _ ih =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ; unfold substAt
      exact CDeriv.impI (by simpa using ih ((φb, Mult.many) :: Γl) Γr Δ Γr' rfl dN hc)
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne dMe dNe hj hdup ihM ihN =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      -- **DILL tightening pays off here.** The argument's context is `NoOne`
      -- (`hdup`), so the `one` hole CANNOT land in the argument (`m₂ ≠ one`);
      -- hence `m₁ = one` is FORCED — the linear cut always routes to the
      -- function premise, and the argument is dropped at tag `zero`.
      have hm2 : m₂ ≠ Mult.one := (noOne_cons.1 (noOne_append.1 hdup).2).1
      have hone : m₁ = Mult.one := by
        cases hmj with
        | zl _ => exact absurd rfl hm2
        | zr _ => rfl
      subst hone
      have hm2z := mjoin_one_left hmj; subst hm2z
      obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
      have hM := ihM Γl₁ Γr₁ Δ Δr rfl dN hADr
      have hN := cderiv_dropZero_aux φ N dNe Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.impE hM hN (cjoin_append hjl hADBr) (noOne_drop_middle hdup)
  | @lolliI Γ φb ψb Mb _ ih =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ; unfold substAt
      exact CDeriv.lolliI (by simpa using ih ((φb, Mult.one) :: Γl) Γr Δ Γr' rfl dN hc)
  | @lolliE Γ Γ₁ Γ₂ φe ψe Me Ne dMe dNe hj ihM ihN =>
      -- The LINEAR arrow's argument is unrestricted, so the `one` hole may route
      -- to EITHER premise — both branches kept (the untightened routing).
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl dN hADr
          have hN := cderiv_dropZero_aux φ N dNe Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.lolliE hM hN (cjoin_append hjl hADBr)
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hM := cderiv_dropZero_aux φ N dMe Γl₁ Γr₁ rfl
          have hN := ihN Γl₂ Γr₂ Δ Δr rfl dN hADr
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.lolliE hM hN (cjoin_append hjl (cjoin_comm hADBr))
  | @tensorI Γ Γ₁ Γ₂ φt ψt Mt Nt dMt dNt hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl dN hADr
          have hN := cderiv_dropZero_aux φ N dNt Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.tensorI hM hN (cjoin_append hjl hADBr)
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hM := cderiv_dropZero_aux φ N dMt Γl₁ Γr₁ rfl
          have hN := ihN Γl₂ Γr₂ Δ Δr rfl dN hADr
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.tensorI hM hN (cjoin_append hjl (cjoin_comm hADBr))
  | @tensorE Γ Γ₁ Γ₂ φt ψt χt St Bt dS dB hj ihS ihB =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hS := ihS Γl₁ Γr₁ Δ Δr rfl dN hADr
          rw [hn1] at hS
          have hB := cderiv_dropZero_aux φ N dB
            ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ rfl
          refine CDeriv.tensorE hS ?_ (cjoin_append hjl hADBr)
          simpa [hn2] using hB
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hS := cderiv_dropZero_aux φ N dS Γl₁ Γr₁ rfl
          rw [hn1] at hS
          have hB := ihB ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ Δ Δr rfl dN hADr
          refine CDeriv.tensorE hS ?_ (cjoin_append hjl (cjoin_comm hADBr))
          simpa [hn2] using hB
  | @saysE Γ Γ₁ Γ₂ p φs ψs Ms Nb dMs dNb hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl dN hADr
          rw [hn1] at hM
          have hNb := cderiv_dropZero_aux φ N dNb ((φs, Mult.many) :: Γl₂) Γr₂ rfl
          refine CDeriv.saysE hM ?_ (cjoin_append hjl hADBr)
          simpa [hn2] using hNb
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hM := cderiv_dropZero_aux φ N dMs Γl₁ Γr₁ rfl
          rw [hn1] at hM
          have hNb := ihN ((φs, Mult.many) :: Γl₂) Γr₂ Δ Δr rfl dN hADr
          refine CDeriv.saysE hM ?_ (cjoin_append hjl (cjoin_comm hADBr))
          simpa [hn2] using hNb
  | @delegate Γ Γ₁ Γ₂ p q φd Md Nd dMd dNd hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl dN hADr
          have hNd := cderiv_dropZero_aux φ N dNd Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.delegate hM hNd (cjoin_append hjl hADBr)
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hM := cderiv_dropZero_aux φ N dMd Γl₁ Γr₁ rfl
          have hNd := ihN Γl₂ Γr₂ Δ Δr rfl dN hADr
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.delegate hM hNd (cjoin_append hjl (cjoin_comm hADBr))
  | @discharge Γ Γ₁ Γ₂ O φd Md Nd dMd dNd hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl dN hADr
          have hNd := cderiv_dropZero_aux φ N dNd Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.discharge hM hNd (cjoin_append hjl hADBr)
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hM := cderiv_dropZero_aux φ N dMd Γl₁ Γr₁ rfl
          have hNd := ihN Γl₂ Γr₂ Δ Δr rfl dN hADr
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.discharge hM hNd (cjoin_append hjl (cjoin_comm hADBr))
  | @letSaysE Γ Γ₁ Γ₂ p φs ψs St Bt dS dB hj ihS ihB =>
      intro Γl Γr Δ Γr' hΓ dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases hone : m₁ = Mult.one
      ·
          subst hone
          have hm2 := mjoin_one_left hmj; subst hm2
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hS := ihS Γl₁ Γr₁ Δ Δr rfl dN hADr
          rw [hn1] at hS
          have hB := cderiv_dropZero_aux φ N dB ((φs, Mult.many) :: Γl₂) Γr₂ rfl
          refine CDeriv.letSaysE hS ?_ (cjoin_append hjl hADBr)
          simpa [hn2] using hB
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hS := cderiv_dropZero_aux φ N dS Γl₁ Γr₁ rfl
          rw [hn1] at hS
          have hB := ihB ((φs, Mult.many) :: Γl₂) Γr₂ Δ Δr rfl dN hADr
          refine CDeriv.letSaysE hS ?_ (cjoin_append hjl (cjoin_comm hADBr))
          simpa [hn2] using hB

/-- **Linear (L4) substitution preservation over `CDeriv`.** The CUT rule:
substituting `N : φ` — carrying its OWN resources `Δ` — for the LINEAR
(`Mult.one`) hypothesis at position `Γl.length` preserves the CARVe judgment,
`CJoin`-MERGING `N`'s resource vector into `M`'s leftover at the positions after
the hole (`CJoin Γr Δ Γr'`, usage-vector addition). Proved for ALL nine
constructors. The linear-algebra substitution step of Wood–Atkey
(arXiv:2005.02247) on the real `Term`/`Prop'`. -/
noncomputable def cderiv_substL {Γl Γr Δ Γr' : Carve.Ctx Prop'} {φ ψ : Prop'}
    {M N : Term}
    (dM : CDeriv (Γl ++ (φ, Mult.one) :: Γr) M ψ)
    (dN : CDeriv Δ N φ)
    (hc : CJoin Γr Δ Γr') :
    CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ :=
  cderiv_substL_aux φ N dM Γl Γr Δ Γr' rfl dN hc

/-! ## Increment 3c — OPEN ADDITIVE (`many`) substitution, the SCALED variant.

Substituting `N : φ` — carrying its OWN resources `Δ` — for the ADDITIVE
(`Mult.many`) hypothesis at position `Γl.length`, where `N`'s context does NOT
vanish (unlike 3a's closed `zeroed Γr`). Per Quantitative Type Theory (Atkey,
LICS 2018) the substitution lemma **scales the substituend's usage vector by the
binder multiplicity and adds it to the context** — here the multiplicity is
`many`, so the merged context is `Γr ⊕ (many · Δ)` (`scaleCtx Mult.many Δ`).

**The scaling/soundness point.** A `many` binder may DUPLICATE `N` (use it
`0..n` times), so any LINEAR (`one`) resource `N` consumes would be used many
times — unsound (a linear resource cannot be copied). Scaling turns each of `N`'s
tags `t` into `many · t`: `many·zero = zero`, `many·one = many`, `many·many =
many` — i.e. it BUMPS every `one` up to `many`. The result `scaleCtx Mult.many Δ`
is therefore always duplicable (`NoOne`, no `one` tags), and `many·many = many`
(`MJoin.mm`) is exactly what lets `N`'s resources merge into BOTH branches of a
`CJoin` when the `many` hole is shared (`MJoin many many many`) — the copy is
idempotent, so merging `Δ` twice equals merging it once.

The genuinely-faithful, PROVABLE statement therefore requires `N` to be typed
under an already-duplicable context (`NoOne Δ`); this is not a weakening but the
soundness condition itself, since bumping `one → many` on a live linear resource
is the unsound direction. The top-level `cderiv_substM_scaled` recovers the QTT
`scaleCtx many` form directly: `scaleCtx Mult.many Δ` is duplicable for any `Δ`,
so a proof of `CDeriv (scaleCtx Mult.many Δ) N φ` feeds the `NoOne` lemma.

Proved over ALL NINE constructors. Content beyond 3b (the `one` cut):
- **the split is 3-way, not 2-way.** A `many` hole splits `MJoin m₁ m₂ many` into
  `(zero,many)`, `(many,zero)` OR `(many,many)` (`mjoin_many_ne_zero`). The first
  two mirror 3b exactly (drop the `zero` branch via `cderiv_dropZero_aux`, recurse
  the other with `Δ` reassociated by `cjoin_reassoc`). The `(many,many)` case is
  NEW: BOTH branches consume `N`, so `Δ` is DUPLICATED into each and the two
  results merge — a duplicating reassociation `cjoin_dup_reassoc` whose
  elementwise core `mjoin_dup` needs `many·many = many` and `d ≠ one`.
- **the var hit is identical to 3b.** At a leaf the `many` hole is still FORCED
  (a `many` tag at any OTHER position violates `AllZeroExcept`), `Γr` collapses
  all-`zero`, the merge `Γr'` equals `Δ`, and `cderiv_shift` places `N` once.

This is the variant subject reduction (increment 4) will consume for the
`many`-binder β-redexes — `imp`/`says`/`delegate`/`discharge`; the `one`-binder
`tensorE` β-redex is covered by 3b's `cderiv_substL`.

Prior art (web-searched 2026-07-22):
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018): the
  substitution lemma multiplies the substituted term's usage by the number of
  times the variable is needed and adds it to the resource context — exactly
  the `many · Δ` scaling. https://bentnib.org/quantitative-type-theory.pdf
- Brady, *Idris 2: Quantitative Type Theory in Practice* (ECOOP 2021): the
  `{0,1,ω}` multiplicity algebra with `ω·1 = ω`, `ω·0 = 0` (our `mscale many`).
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol194-ecoop2021/LIPIcs.ECOOP.2021.9/LIPIcs.ECOOP.2021.9.pdf
- Wood & Atkey, *A Linear Algebra Approach to Linear Metatheory* (arXiv:2005.02247):
  simultaneous substitution as a usage-respecting environment; scaling and
  addition are the semiring `*`/`+`. https://arxiv.org/abs/2005.02247
- Abel, Danielsson & Eriksson, *A Graded Modal Dependent Type Theory … Formalized*
  (ICFP 2023): a machine-checked substitution theorem for grade assignment over
  a partially-ordered-semiring modality — the same scale-and-add discipline.
  https://www.cse.chalmers.se/~nad/publications/abel-danielsson-eriksson-graded-type-theory.pdf -/

/-- Tag scaling `m · t` in the resource algebra. For `m = many`:
`many·zero = zero`, `many·one = many`, `many·many = many` — the QTT `ω·`
(Idris-2 `{0,1,ω}`: `ω·1 = ω`, `ω·0 = 0`). It BUMPS `one` to `many`, which is
what makes a linear resource of `N` un-duplicable-safe under a `many` binder. -/
def mscale : Mult → Mult → Mult
  | Mult.zero, _ => Mult.zero
  | Mult.one,  d => d
  | Mult.many, Mult.zero => Mult.zero
  | Mult.many, _ => Mult.many

/-- QTT context scaling: multiply every tag of `Δ` by `m`. `scaleCtx Mult.many`
is the usage vector the substitution lemma ADDS to the context at a `many`
binder. -/
def scaleCtx (m : Mult) (Δ : Carve.Ctx Prop') : Carve.Ctx Prop' :=
  Δ.map (fun p => (p.1, mscale m p.2))

/-- `scaleCtx Mult.many Δ` is always duplicable: `mscale many` lands only in
`{zero, many}`, never `one`. This is what lets the QTT-faithful
`cderiv_substM_scaled` feed the `NoOne` hypothesis for an arbitrary `Δ`. -/
theorem noOne_scaleCtx_many (Δ : Carve.Ctx Prop') : NoOne (scaleCtx Mult.many Δ) := by
  intro p hp
  simp only [scaleCtx, List.mem_map] at hp
  obtain ⟨q, _hq, hpq⟩ := hp
  rw [← hpq]
  show mscale Mult.many q.2 ≠ Mult.one
  cases q.2 <;> decide

/-- When `Δ` is ALREADY duplicable, `many`-scaling is the identity — the scaling
is only observable on the (excluded, unsound) `one` tags. Documents that the
`NoOne` form and the `scaleCtx Mult.many` form coincide on their common domain. -/
theorem scaleCtx_many_of_noOne :
    ∀ (Δ : Carve.Ctx Prop'), NoOne Δ → scaleCtx Mult.many Δ = Δ
  | [], _ => rfl
  | (a, d) :: tl, h => by
      have hd : d ≠ Mult.one := h (a, d) (List.mem_cons_self)
      have htl := scaleCtx_many_of_noOne tl (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have hdd : mscale Mult.many d = d := by cases d <;> first | rfl | exact absurd rfl hd
      simp only [scaleCtx, List.map_cons] at htl ⊢
      rw [hdd, htl]

/-- `madd a Mult.zero = a` — `zero` is the additive unit on the right. -/
theorem madd_zero (a : Mult) : madd a Mult.zero = a := by cases a <;> rfl

/-- **The elementwise duplicating reassociation.** From `a₁ ⊕ a₂ = a` and
`a ⊕ d = a'` with `d` DUPLICABLE (`d ≠ one`), route `d` into BOTH summands:
`a₁ ⊕ d = madd a₁ d`, `a₂ ⊕ d = madd a₂ d`, and those two rejoin to `a'`. The
`d = many` shared case rests on `many ⊕ many = many` (`MJoin.mm`, idempotent) —
the copy is free. This is the `(many,many)` heart of the scaled substitution. -/
theorem mjoin_dup {a₁ a₂ a d a' : Mult}
    (h1 : MJoin a₁ a₂ a) (h2 : MJoin a d a') (hd : d ≠ Mult.one) :
    MJoin a₁ d (madd a₁ d) ∧ MJoin a₂ d (madd a₂ d)
      ∧ MJoin (madd a₁ d) (madd a₂ d) a' := by
  cases h2 with
  | zl _ =>
      obtain ⟨e1, e2⟩ := mjoin_zero h1
      subst e1; subst e2
      refine ⟨MJoin.zl _, MJoin.zl _, ?_⟩
      simp only [madd]
      cases d with
      | zero => exact MJoin.zl _
      | one => exact absurd rfl hd
      | many => exact MJoin.mm
  | zr _ =>
      simp only [madd_zero]
      exact ⟨MJoin.zr _, MJoin.zr _, h1⟩
  | mm =>
      cases h1 with
      | zl _ => exact ⟨MJoin.zl _, MJoin.mm, MJoin.mm⟩
      | zr _ => exact ⟨MJoin.mm, MJoin.zl _, MJoin.mm⟩
      | mm => exact ⟨MJoin.mm, MJoin.mm, MJoin.mm⟩

/-- A `many` result splits three ways: `(zero,many)`, `(many,zero)` or
`(many,many)`. Stated as the "neither is `zero`" case (both `many`), the other
two handled by `mjoin_zero_left`/`_right`; split on tag DATA (decidable
`= zero`), never by `cases` on the `Prop`-valued `MJoin` into `Type`. -/
theorem mjoin_many_ne_zero {m₁ m₂ : Mult} (h : MJoin m₁ m₂ Mult.many)
    (h1 : m₁ ≠ Mult.zero) (h2 : m₂ ≠ Mult.zero) : m₁ = Mult.many ∧ m₂ = Mult.many := by
  cases h with
  | zl _ => exact absurd rfl h1
  | zr _ => exact absurd rfl h2
  | mm => exact ⟨rfl, rfl⟩

/-- A `zero` LEFT summand of a `many` join forces the right summand `many`. -/
theorem mjoin_zero_left {m₂ : Mult} (h : MJoin Mult.zero m₂ Mult.many) : m₂ = Mult.many := by
  cases h with | zl _ => rfl

/-- A `zero` RIGHT summand of a `many` join forces the left summand `many`. -/
theorem mjoin_zero_right {m₁ : Mult} (h : MJoin m₁ Mult.zero Mult.many) : m₁ = Mult.many := by
  cases h with | zr _ => rfl

/-- The duplicating-reassociation result at the context level: the two per-branch
merges plus the rejoin. Sibling of `CReassoc`, but `Δ` reaches BOTH sides. -/
structure CDup (Γr₁ Γr₂ Δ Γr' : Carve.Ctx Prop') : Type where
  Γr₁' : Carve.Ctx Prop'
  Γr₂' : Carve.Ctx Prop'
  h1 : CJoin Γr₁ Δ Γr₁'
  h2 : CJoin Γr₂ Δ Γr₂'
  h3 : CJoin Γr₁' Γr₂' Γr'

/-- **`CJoin` duplicating reassociation** (elementwise `mjoin_dup`). From
`Γr₁ ⊕ Γr₂ = Γr` and `Γr ⊕ Δ = Γr'` with `Δ` DUPLICABLE (`NoOne`), merge `Δ`
into EACH of `Γr₁`, `Γr₂` and rejoin to `Γr'`. This is the `(many,many)`
subject-reduction step: a shared `many` binder copies `N`'s resources into both
premises, sound precisely because `Δ` has no linear tag. -/
noncomputable def cjoin_dup_reassoc :
    ∀ {Γr₁ Γr₂ Γr : Carve.Ctx Prop'}, CJoin Γr₁ Γr₂ Γr →
      ∀ {Δ Γr' : Carve.Ctx Prop'}, CJoin Γr Δ Γr' → NoOne Δ → CDup Γr₁ Γr₂ Δ Γr' := by
  intro Γr₁ Γr₂ Γr hjr
  induction hjr with
  | nil =>
      intro Δ Γr' hc _
      cases hc
      exact ⟨[], [], CJoin.nil, CJoin.nil, CJoin.nil⟩
  | @cons x b₁ b₂ b Γ1 Γ2 Γ hmb _ ih =>
      intro Δ Γr' hc hd
      cases hc with
      | @cons _ _ dd bprime _ Δt _ hmd hcrest =>
          have hdne : dd ≠ Mult.one := hd (x, dd) (List.mem_cons_self)
          have hdtail : NoOne Δt := fun p hp => hd p (List.mem_cons_of_mem _ hp)
          obtain ⟨j1, j2, j3⟩ := mjoin_dup hmb hmd hdne
          let r := ih hcrest hdtail
          exact ⟨(x, madd b₁ dd) :: r.Γr₁', (x, madd b₂ dd) :: r.Γr₂',
                 CJoin.cons j1 r.h1, CJoin.cons j2 r.h2, CJoin.cons j3 r.h3⟩

/-- **Open additive (scaled L4) substitution preservation (auxiliary, all nine
constructors).** `φ`/`N` fixed; the hole tag is `Mult.many`, `Δ` duplicable
(`NoOne`). At the single `var` leaf the hole is FORCED (a `many` elsewhere
violates `AllZeroExcept`), `Γr` collapses all-`zero`, so `Γr' = Δ` and `N` is
placed once via `cderiv_shift`. At each `CJoin` premise the `many` splits 3-way:
`(zero,·)`/`(·,zero)` drop one branch (`cderiv_dropZero_aux`) and reassociate `Δ`
past the other (`cjoin_reassoc`); `(many,many)` DUPLICATES `Δ` into both branches
(`cjoin_dup_reassoc`) and rejoins. Split on the tag DATA (`by_cases … = zero`),
since `MJoin : Prop` cannot eliminate into the `Type`-valued `CDeriv`. -/
private noncomputable def cderiv_substM_aux {Γfull : Carve.Ctx Prop'} {M : Term}
    {ψ : Prop'} (φ : Prop') (N : Term) (dM : CDeriv Γfull M ψ) :
    ∀ (Γl Γr Δ Γr' : Carve.Ctx Prop'), Γfull = Γl ++ (φ, Mult.many) :: Γr →
      NoOne Δ → CDeriv Δ N φ → CJoin Γr Δ Γr' →
      CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ := by
  induction dM with
  | @var Γ i χ mvar h hmvar hz =>
      intro Γl Γr Δ Γr' hΓ _ dN hc
      subst hΓ
      unfold substAt
      -- The `many` hole forces this leaf to hit it (`AllZeroExcept`).
      have heq : i = Γl.length := by
        by_contra hne
        have hzero := hz Γl.length (φ, Mult.many) (fun he => hne he.symm)
          (by rw [List.getElem?_append_right (le_refl Γl.length)]; simp)
        simp at hzero
      rw [if_pos heq]
      rw [heq] at h hz
      obtain ⟨hzl, hzr⟩ := allZeroExcept_split_zeroed hz
      rw [List.getElem?_append_right (le_refl Γl.length)] at h
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hφχ, _⟩ := h
      subst hφχ
      have heE : Γr' = Δ := cjoin_left_all_zero hc hzr
      subst Γr'
      have hshift := cderiv_shift dN [] Γl Δ (by simp)
      simp only [List.nil_append, List.length_nil] at hshift
      rwa [← hzl] at hshift
  | @impI Γ φb ψb Mb _ ih =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ; unfold substAt
      exact CDeriv.impI (by simpa using ih ((φb, Mult.many) :: Γl) Γr Δ Γr' rfl hd dN hc)
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne dMe dNe hj hdup ihM ihN =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      obtain ⟨hnl, hnr'⟩ := noOne_append.1 hdup
      have hnr : NoOne Γr₂ := (noOne_cons.1 hnr').2
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hM := cderiv_dropZero_aux φ N dMe Γl₁ Γr₁ rfl
        have hN := ihN Γl₂ Γr₂ Δ Δr rfl hd dN hADr
        rw [hn1] at hM; rw [hn2] at hN
        exact CDeriv.impE hM hN (cjoin_append hjl (cjoin_comm hADBr))
          (noOne_append.2 ⟨hnl, noOne_cjoin_merge hnr hd hADr⟩)
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          have hN := cderiv_dropZero_aux φ N dNe Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.impE hM hN (cjoin_append hjl hADBr) (noOne_drop_middle hdup)
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hM := ihM Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          have hN := ihN Γl₂ Γr₂ Δ Δ2 rfl hd dN hj2
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.impE hM hN (cjoin_append hjl hj3)
            (noOne_append.2 ⟨hnl, noOne_cjoin_merge hnr hd hj2⟩)
  | @lolliI Γ φb ψb Mb _ ih =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ; unfold substAt
      exact CDeriv.lolliI (by simpa using ih ((φb, Mult.one) :: Γl) Γr Δ Γr' rfl hd dN hc)
  | @lolliE Γ Γ₁ Γ₂ φe ψe Me Ne dMe dNe hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hM := cderiv_dropZero_aux φ N dMe Γl₁ Γr₁ rfl
        have hN := ihN Γl₂ Γr₂ Δ Δr rfl hd dN hADr
        rw [hn1] at hM; rw [hn2] at hN
        exact CDeriv.lolliE hM hN (cjoin_append hjl (cjoin_comm hADBr))
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          have hN := cderiv_dropZero_aux φ N dNe Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.lolliE hM hN (cjoin_append hjl hADBr)
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hM := ihM Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          have hN := ihN Γl₂ Γr₂ Δ Δ2 rfl hd dN hj2
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.lolliE hM hN (cjoin_append hjl hj3)
  | @tensorI Γ Γ₁ Γ₂ φt ψt Mt Nt dMt dNt hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hM := cderiv_dropZero_aux φ N dMt Γl₁ Γr₁ rfl
        have hN := ihN Γl₂ Γr₂ Δ Δr rfl hd dN hADr
        rw [hn1] at hM; rw [hn2] at hN
        exact CDeriv.tensorI hM hN (cjoin_append hjl (cjoin_comm hADBr))
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          have hN := cderiv_dropZero_aux φ N dNt Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.tensorI hM hN (cjoin_append hjl hADBr)
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hM := ihM Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          have hN := ihN Γl₂ Γr₂ Δ Δ2 rfl hd dN hj2
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.tensorI hM hN (cjoin_append hjl hj3)
  | @tensorE Γ Γ₁ Γ₂ φt ψt χt St Bt dS dB hj ihS ihB =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hS := cderiv_dropZero_aux φ N dS Γl₁ Γr₁ rfl
        rw [hn1] at hS
        have hB := ihB ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ Δ Δr rfl hd dN hADr
        refine CDeriv.tensorE hS ?_ (cjoin_append hjl (cjoin_comm hADBr))
        simpa [hn2] using hB
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hS := ihS Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          rw [hn1] at hS
          have hB := cderiv_dropZero_aux φ N dB
            ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ rfl
          refine CDeriv.tensorE hS ?_ (cjoin_append hjl hADBr)
          simpa [hn2] using hB
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hS := ihS Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          rw [hn1] at hS
          have hB := ihB ((φt, Mult.one) :: (ψt, Mult.one) :: Γl₂) Γr₂ Δ Δ2 rfl hd dN hj2
          refine CDeriv.tensorE hS ?_ (cjoin_append hjl hj3)
          simpa [hn2] using hB
  | @saysE Γ Γ₁ Γ₂ p φs ψs Ms Nb dMs dNb hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hM := cderiv_dropZero_aux φ N dMs Γl₁ Γr₁ rfl
        rw [hn1] at hM
        have hNb := ihN ((φs, Mult.many) :: Γl₂) Γr₂ Δ Δr rfl hd dN hADr
        refine CDeriv.saysE hM ?_ (cjoin_append hjl (cjoin_comm hADBr))
        simpa [hn2] using hNb
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          rw [hn1] at hM
          have hNb := cderiv_dropZero_aux φ N dNb ((φs, Mult.many) :: Γl₂) Γr₂ rfl
          refine CDeriv.saysE hM ?_ (cjoin_append hjl hADBr)
          simpa [hn2] using hNb
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hM := ihM Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          rw [hn1] at hM
          have hNb := ihN ((φs, Mult.many) :: Γl₂) Γr₂ Δ Δ2 rfl hd dN hj2
          refine CDeriv.saysE hM ?_ (cjoin_append hjl hj3)
          simpa [hn2] using hNb
  | @delegate Γ Γ₁ Γ₂ p q φd Md Nd dMd dNd hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hM := cderiv_dropZero_aux φ N dMd Γl₁ Γr₁ rfl
        have hNd := ihN Γl₂ Γr₂ Δ Δr rfl hd dN hADr
        rw [hn1] at hM; rw [hn2] at hNd
        exact CDeriv.delegate hM hNd (cjoin_append hjl (cjoin_comm hADBr))
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          have hNd := cderiv_dropZero_aux φ N dNd Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.delegate hM hNd (cjoin_append hjl hADBr)
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hM := ihM Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          have hNd := ihN Γl₂ Γr₂ Δ Δ2 rfl hd dN hj2
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.delegate hM hNd (cjoin_append hjl hj3)
  | @discharge Γ Γ₁ Γ₂ O φd Md Nd dMd dNd hj ihM ihN =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hM := cderiv_dropZero_aux φ N dMd Γl₁ Γr₁ rfl
        have hNd := ihN Γl₂ Γr₂ Δ Δr rfl hd dN hADr
        rw [hn1] at hM; rw [hn2] at hNd
        exact CDeriv.discharge hM hNd (cjoin_append hjl (cjoin_comm hADBr))
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hM := ihM Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          have hNd := cderiv_dropZero_aux φ N dNd Γl₂ Γr₂ rfl
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.discharge hM hNd (cjoin_append hjl hADBr)
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hM := ihM Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          have hNd := ihN Γl₂ Γr₂ Δ Δ2 rfl hd dN hj2
          rw [hn1] at hM; rw [hn2] at hNd
          exact CDeriv.discharge hM hNd (cjoin_append hjl hj3)
  | @letSaysE Γ Γ₁ Γ₂ p φs ψs St Bt dS dB hj ihS ihB =>
      intro Γl Γr Δ Γr' hΓ hd dN hc
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2; unfold substAt
      by_cases h1z : m₁ = Mult.zero
      · subst h1z
        have h2m := mjoin_zero_left hmj; subst h2m
        obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
        have hS := cderiv_dropZero_aux φ N dS Γl₁ Γr₁ rfl
        rw [hn1] at hS
        have hB := ihB ((φs, Mult.many) :: Γl₂) Γr₂ Δ Δr rfl hd dN hADr
        refine CDeriv.letSaysE hS ?_ (cjoin_append hjl (cjoin_comm hADBr))
        simpa [hn2] using hB
      · by_cases h2z : m₂ = Mult.zero
        · subst h2z
          have h1m := mjoin_zero_right hmj; subst h1m
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc hjr hc
          have hS := ihS Γl₁ Γr₁ Δ Δr rfl hd dN hADr
          rw [hn1] at hS
          have hB := cderiv_dropZero_aux φ N dB ((φs, Mult.many) :: Γl₂) Γr₂ rfl
          refine CDeriv.letSaysE hS ?_ (cjoin_append hjl hADBr)
          simpa [hn2] using hB
        · obtain ⟨h1m, h2m⟩ := mjoin_many_ne_zero hmj h1z h2z
          subst h1m; subst h2m
          obtain ⟨Δ1, Δ2, hj1, hj2, hj3⟩ := cjoin_dup_reassoc hjr hc hd
          have hS := ihS Γl₁ Γr₁ Δ Δ1 rfl hd dN hj1
          rw [hn1] at hS
          have hB := ihB ((φs, Mult.many) :: Γl₂) Γr₂ Δ Δ2 rfl hd dN hj2
          refine CDeriv.letSaysE hS ?_ (cjoin_append hjl hj3)
          simpa [hn2] using hB

/-- **Open additive (scaled L4) substitution preservation over `CDeriv`.**
Substituting `N : φ` — carrying its OWN DUPLICABLE resources `Δ` (`NoOne Δ`) —
for the ADDITIVE (`Mult.many`) hypothesis at position `Γl.length` preserves the
CARVe judgment, `CJoin`-MERGING `Δ` into `M`'s leftover after the hole. The
`NoOne` requirement is the QTT scaling made honest: a `many` binder duplicates
`N`, so `N`'s linear (`one`) resources would be copied — unsound — hence `Δ` must
already be one-free. Proved for ALL nine constructors. (Compose with
`cderiv_substM_scaled` to recover the `scaleCtx Mult.many Δ` form for arbitrary
`Δ`.) -/
noncomputable def cderiv_substM {Γl Γr Δ Γr' : Carve.Ctx Prop'} {φ ψ : Prop'}
    {M N : Term}
    (dM : CDeriv (Γl ++ (φ, Mult.many) :: Γr) M ψ)
    (dN : CDeriv Δ N φ)
    (hdup : NoOne Δ)
    (hc : CJoin Γr Δ Γr') :
    CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ :=
  cderiv_substM_aux φ N dM Γl Γr Δ Γr' rfl hdup dN hc

/-- **The QTT-faithful scaled form.** For an ARBITRARY `Δ`, substituting `N : φ`
typed under the scaled context `scaleCtx Mult.many Δ` for a `many` hypothesis
merges `scaleCtx Mult.many Δ` into the leftover — the Atkey (LICS 2018)
substitution lemma "scale the substituend's usage by the binder multiplicity and
add it". Duplicability is automatic (`noOne_scaleCtx_many`): `many`-scaling bumps
every `one` to `many`, so the scaled context is always one-free. -/
noncomputable def cderiv_substM_scaled {Γl Γr Δ Γr' : Carve.Ctx Prop'} {φ ψ : Prop'}
    {M N : Term}
    (dM : CDeriv (Γl ++ (φ, Mult.many) :: Γr) M ψ)
    (dN : CDeriv (scaleCtx Mult.many Δ) N φ)
    (hc : CJoin Γr (scaleCtx Mult.many Δ) Γr') :
    CDeriv (Γl ++ Γr') (substAt M N Γl.length) ψ :=
  cderiv_substM dM dN (noOne_scaleCtx_many Δ) hc

/-! ## Increment 4a — subject reduction (preservation) for `CDeriv`.

`CDeriv Γ M ψ → step M = some M' → CDeriv Γ M' ψ`, over DLC's real deterministic
`step` (`DLC.Reduce`), for the CARVe judgment. Standard structure: induction on
the derivation, per-redex + ξ-congruence, with the substitution triad closing
the β cases. The scope precisely characterised below (see also the module-header
"Scope of increment 4a").

**Which redexes actually fire in this fragment.** `step`'s eight head redexes
guard on the SCRUTINEE'S INTRO form. Only two of those intro forms are inhabited
by `CDeriv` (which has `lam` and `tensorIntro` but NO `sign`/`boxed`/`pair`/…
introduction):
- **imp-β** `app (lam φ B) N ▷ subst B N` — `impI` binds `(φ, many)`. FIRES.
- **tensor-E-β** `letTensor (tensorIntro a b) B ▷ subst (subst B (shift a 1 0)) b`
  — `tensorE` binds two `(·, one)`. FIRES. The load-bearing LINEAR case.

Every OTHER head redex (`says`/`letSays`/`delegate`/`discharge` extraction) needs
a `sign`/`boxed` scrutinee; `CDeriv` has no rule concluding those, so the
scrutinee's derivation is UNINHABITED and the head branch closes by `cases`
(mirroring `DLC.Decidability`'s `discharge` case) — only ξ-congruence descends.
ξ-congruence is uniform: step the sub-term, rebuild the same constructor via the
IH. Value/frozen subjects (`var`, `lam`, `tensorIntro`) give `step = none`.

**The imp-β soundness finding (EXPOSED, not hidden).** `impI` binds `(φ, many)`
(the argument is UNRESTRICTED/duplicable) but `impE` admits `N` under an
ARBITRARY context `Γ₂` — including `one` (linear) tags. imp-β preservation runs
through `cderiv_substM`, which demands `NoOne Γ₂` (`N` duplicable). This side
condition is NOT gratuitous: WITHOUT it preservation genuinely FAILS. Take
`(λ^many x. x ⊗ x) N` where `N : φ` consumes a LINEAR resource (`Γ₂` has a `one`).
The redex is well-typed (`impE` of a `many`-abstraction to a linearly-resourced
`N`), but it reduces to `N ⊗ N`, which is NOT typable: `tensorI` would split `Γ`
so that BOTH sides type `N`, requiring the shared `one` tag to route to two
non-zero summands — impossible (`mjoin_one_not_shared`). So a `many` (additive
`⊃`) β-redex DUPLICATES a linear argument. The precise result:
  - `cderiv_imp_beta` proves imp-β preservation UNDER the exact side condition
    `NoOne Γ₂` (`N`'s context duplicable);
  - the top-level `cderiv_subject_reduction` holds on the fragment `NoOne Γ`
    (the ambient context carries no LIVE linear resource). `NoOne` PROPAGATES to
    every position `step` can reach — `step` never crosses a binder, and `CJoin`
    preserves `NoOne` (`noOne_cjoin`, via `mjoin_ne_one`) — so on this fragment
    the imp-β argument is always duplicable and the redex is sound. The linear
    (`one`) binders of `tensorE` live INSIDE the body's context, never in `Γ`, so
    `NoOne Γ` does NOT trivialise the load-bearing tensor-β.

The finding in one line: DLC's `imp` (additive `⊃`, `many`-binder) is subject-
reduction-sound exactly when its arguments are duplicable; a linear argument
belongs to a linear function type (`⊸`/one-binder), not to `imp`. This is the
QTT/Wood–Atkey discipline: β-substituting a `many` variable SCALES the
substituend's usage by `many` (`cderiv_substM_scaled`), and scaling a live `one`
is the unsound direction.

Prior art (web-searched 2026-07-22): subject reduction for linear/graded calculi
is proved via the substitution lemma, per redex, with SEPARATE substitution
lemmas for the LINEAR variable (usage adds — `cderiv_substL`) and the
UNRESTRICTED variable (usage scales then adds — `cderiv_substM`); the additive-β
/ linear-resource interaction (a `many`-binder duplicating a linear argument) is
exactly why linear arguments must sit at `⊸`, not `⊃`.
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018): the
  substitution lemma scales the substituend's usage by the binder multiplicity;
  subject reduction follows. https://bentnib.org/quantitative-type-theory.pdf
- Wood & Atkey, *A Linear Algebra Approach to Linear Metatheory* (arXiv:2005.02247):
  linear systems do NOT validate naive substitution; the usage-respecting
  environment method (linear + unrestricted substitution lemmas) is the fix.
  https://arxiv.org/abs/2005.02247
- Wood & Atkey, *A Framework for Substructural Type Systems* (ESOP 2022):
  https://bentnib.org/quant-framework.pdf
- "Subject Reduction — an overview" (ScienceDirect): subject reduction of linear
  typing systems follows from the Linear Substitution Lemma, per redex.
  https://www.sciencedirect.com/topics/computer-science/subject-reduction -/

/-- **`NoOne` propagates through a split.** If the joined context has no LINEAR
(`one`) tag, then neither operand does: `MJoin m₁ m₂ m` with `m ≠ one` forces
`m₁ ≠ one ∧ m₂ ≠ one` (`mjoin_ne_one`). This is what lets `NoOne Γ` descend to
every premise `step` reaches — and, at an imp-β, delivers the `NoOne Γ₂` that
`cderiv_imp_beta` needs. -/
theorem noOne_cjoin {Γ₁ Γ₂ Γ : Carve.Ctx Prop'} (h : CJoin Γ₁ Γ₂ Γ) :
    NoOne Γ → NoOne Γ₁ ∧ NoOne Γ₂ := by
  induction h with
  | nil => intro _; exact ⟨by intro p hp; simp at hp, by intro p hp; simp at hp⟩
  | @cons a m₁ m₂ m Δ₁ Δ₂ Δ hm _ ih =>
      intro hΓ
      have hm_ne : m ≠ Mult.one := hΓ (a, m) List.mem_cons_self
      have hΔ : NoOne Δ := fun p hp => hΓ p (List.mem_cons_of_mem _ hp)
      obtain ⟨hd1, hd2⟩ := ih hΔ
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hm hm_ne
      exact ⟨noOne_cons.mpr ⟨hm1, hd1⟩, noOne_cons.mpr ⟨hm2, hd2⟩⟩

/-- **imp-β preservation, under the exact side condition.** `app (lam φ B) N`
β-reduces to `subst B N`; typing is preserved PROVIDED `N`'s resource context is
DUPLICABLE (`NoOne Γ₂`). This is the honest characterisation of the additive-`⊃`
β-redex: `impI` binds `(φ, many)`, so `N` may be duplicated; the reduct is
well-typed exactly when duplicating `N` is sound, i.e. `N` uses no linear
resource. Proof: the QTT open-additive cut `cderiv_substM`. Without `NoOne Γ₂`
this FAILS (see the section header's counterexample). -/
noncomputable def cderiv_imp_beta {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ : Prop'} {B N : Term}
    (dbody : CDeriv ((φ, Mult.many) :: Γ₁) B ψ)
    (dN : CDeriv Γ₂ N φ)
    (hj : CJoin Γ₁ Γ₂ Γ)
    (hdup : NoOne Γ₂) :
    CDeriv Γ (subst B N) ψ := by
  have h := cderiv_substM (Γl := []) (Γr := Γ₁) (Δ := Γ₂) (Γr' := Γ)
    (φ := φ) (ψ := ψ) (M := B) (N := N) (by simpa using dbody) dN hdup hj
  simpa [subst] using h

/-- **lolli-β preservation, UNCONDITIONAL.** `app (lam φ B) N` β-reduces to
`subst B N`; for a LINEAR function (`lolliI` binds `(φ, one)`) typing is preserved
for an ARBITRARY argument context — NO duplicability side condition. `N` is
consumed exactly once, so its resources simply MERGE (`CJoin`) into the body's
leftover — the linear cut `cderiv_substL`. This is the `⊸`-β twin of
`cderiv_imp_beta`, and the reason a LINEAR argument belongs at `⊸`, not `⊃`. -/
noncomputable def cderiv_lolli_beta {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ : Prop'} {B N : Term}
    (dbody : CDeriv ((φ, Mult.one) :: Γ₁) B ψ)
    (dN : CDeriv Γ₂ N φ)
    (hj : CJoin Γ₁ Γ₂ Γ) :
    CDeriv Γ (subst B N) ψ := by
  have h := cderiv_substL (Γl := []) (Γr := Γ₁) (Δ := Γ₂) (Γr' := Γ)
    (φ := φ) (ψ := ψ) (M := B) (N := N) (by simpa using dbody) dN hj
  simpa [subst] using h

/-- **THE DILL PAYOFF — UNCONDITIONAL subject reduction for `CDeriv`.**
`CDeriv Γ M ψ → step M = some M' → CDeriv Γ M' ψ`, over DLC's real deterministic
`step`, with **NO `NoOne Γ` hypothesis**. Both β-cases are now sound for ALL `Γ`
by construction of the DILL discipline:
- **imp-β** (`impE` head, `f = lam`): `cderiv_imp_beta`, with `NoOne Γ₂` taken
  DIRECTLY from the tightened `impE` constructor (`hdup`) — no longer synthesised
  from an ambient `NoOne Γ`. A `⊃`-redex only ever holds a DUPLICABLE argument.
- **lolli-β** (`lolliE` head, `f = lam`): `cderiv_lolli_beta`, the linear cut
  `cderiv_substL` — UNCONDITIONAL (the argument is consumed once, usage adds).
- **tensor-E-β** (`tensorE` head, `S = tensorIntro`): the LINEAR load-bearing
  case. `cderiv_shift` lifts `a` past the surviving `ψ`-binder, then
  `cderiv_substL` TWICE (two `one` binders), leftovers rerouted by
  `cjoin_reassoc`/`cjoin_comm` — usage-vector addition, no side condition.
- **modal head redexes** (`saysE`/`letSaysE`/`delegate`/`discharge`): the
  scrutinee is `says`/`boxed`-typed; `CDeriv` has no `sign`/`boxed` intro, so the
  head branch closes by `cases` on the uninhabited scrutinee derivation.
- **ξ-congruence** (every elimination): step the sub-term, rebuild via the IH.
- **values/frozen** (`var`, `impI`, `lolliI`, `tensorI`): `step = none`, vacuous.
The imp-β soundness finding of increment 4a is now GUARDED at the type level:
the `NoOne Γ₂` that 4a threaded through an ambient `NoOne Γ` fragment is instead
carried by every `impE` node, so no ambient hypothesis is needed. -/
noncomputable def cderiv_subject_reduction' {Γ : Carve.Ctx Prop'} {M : Term} {ψ : Prop'}
    (d : CDeriv Γ M ψ) :
    ∀ M', step M = some M' → CDeriv Γ M' ψ := by
  induction d with
  | var _ _ _ => intro M' h; simp [step] at h
  | impI _ => intro M' h; simp [step] at h
  | lolliI _ => intro M' h; simp [step] at h
  | tensorI _ _ _ => intro M' h; simp [step] at h
  | @impE Γ Γ₁ Γ₂ φ ψ f x dM dN hj hdup ihM ihN =>
      intro M' h
      unfold step at h
      split at h
      · -- imp-β: `hdup : NoOne Γ₂` comes straight from the tightened `impE`.
        simp only [Option.some.injEq] at h
        subst h
        cases dM with
        | impI dbody => exact cderiv_imp_beta dbody dN hj hdup
      · cases hf : step f with
        | none => simp [hf] at h
        | some f' =>
            simp [hf] at h
            subst h
            exact CDeriv.impE (ihM f' hf) dN hj hdup
  | @lolliE Γ Γ₁ Γ₂ φ ψ f x dM dN hj ihM ihN =>
      intro M' h
      unfold step at h
      split at h
      · -- lolli-β: UNCONDITIONAL linear cut, argument arbitrary.
        simp only [Option.some.injEq] at h
        subst h
        cases dM with
        | lolliI dbody => exact cderiv_lolli_beta dbody dN hj
      · cases hf : step f with
        | none => simp [hf] at h
        | some f' =>
            simp [hf] at h
            subst h
            exact CDeriv.lolliE (ihM f' hf) dN hj
  | @tensorE Γ Γ₁ Γ₂ φ ψ χ S B dS dB hj ihS _ =>
      intro M' h
      unfold step at h
      split at h
      · -- tensor-E-β: S = tensorIntro a b. The LINEAR load-bearing case.
        simp only [Option.some.injEq] at h
        subst h
        cases dS with
        | @tensorI _ Γa Γb _ _ _ _ dSa dSb hjS =>
            obtain ⟨AD, hAD, hADB⟩ := cjoin_reassoc hjS hj
            have dShift := cderiv_shift dSa [] [(ψ, Mult.one)] Γa (by simp)
            have hc1 : CJoin ((ψ, Mult.one) :: Γ₂) ((ψ, Mult.zero) :: Γa)
                ((ψ, Mult.one) :: AD) := CJoin.cons (MJoin.zr Mult.one) (cjoin_comm hAD)
            have step1 := cderiv_substL (Γl := []) (Γr := (ψ, Mult.one) :: Γ₂)
              (Δ := (ψ, Mult.zero) :: Γa) (Γr' := (ψ, Mult.one) :: AD)
              (φ := φ) (ψ := χ) (by simpa using dB) dShift hc1
            have step2 := cderiv_substL (Γl := []) (Γr := AD) (Δ := Γb) (Γr' := Γ)
              (φ := ψ) (ψ := χ) (by simpa using step1) dSb hADB
            simpa [subst] using step2
      · cases hs : step S with
        | none => simp [hs] at h
        | some S' =>
            simp [hs] at h
            subst h
            exact CDeriv.tensorE (ihS S' hs) dB hj
  | @saysE Γ Γ₁ Γ₂ p φ ψ S N dS dN hj ihS _ =>
      intro M' h
      unfold step at h
      split at h
      · cases dS
      · cases hs : step S with
        | none => simp [hs] at h
        | some S' =>
            simp [hs] at h
            subst h
            exact CDeriv.saysE (ihS S' hs) dN hj
  | @delegate Γ Γ₁ Γ₂ p q φ m n dM dN hj ihM _ =>
      intro M' h
      unfold step at h
      split at h
      · cases dM
      · cases dM
      · cases hm : step m with
        | none => simp [hm] at h
        | some m' =>
            simp [hm] at h
            subst h
            exact CDeriv.delegate (ihM m' hm) dN hj
  | @discharge Γ Γ₁ Γ₂ O φ m n dM dN hj ihM _ =>
      intro M' h
      unfold step at h
      split at h
      · cases dM
      · cases hm : step m with
        | none => simp [hm] at h
        | some m' =>
            simp [hm] at h
            subst h
            exact CDeriv.discharge (ihM m' hm) dN hj
  | @letSaysE Γ Γ₁ Γ₂ p φ ψ S B dS dB hj ihS _ =>
      intro M' h
      unfold step at h
      split at h
      · cases dS
      · cases hs : step S with
        | none => simp [hs] at h
        | some S' =>
            simp [hs] at h
            subst h
            exact CDeriv.letSaysE (ihS S' hs) dB hj

/-- **4a's `NoOne Γ`-fragment theorem, retained as a corollary.** The tightening
makes the ambient `NoOne Γ` hypothesis redundant, so this is now the unconditional
result with an ignored premise — kept for API compatibility with increment 4a. -/
noncomputable def cderiv_subject_reduction {Γ : Carve.Ctx Prop'} {M : Term} {ψ : Prop'}
    (d : CDeriv Γ M ψ) :
    NoOne Γ → ∀ M', step M = some M' → CDeriv Γ M' ψ :=
  fun _ => cderiv_subject_reduction' d

/-! ## Progress for `CDeriv` — the second half of type soundness.

Mirrors `DLC.Progress` (`lean/DLC/Progress.lean`): a well-typed CLOSED term is a
value or takes a `step`. DLC's `progress` states this for `PropDeriv [] M φ`; the
CARVe analogue is the **empty resource-vector context** `Γ = []` — the
`NoOne`/empty-linear closedness condition of a linear/DILL fragment. Under
`Γ = []`, `CJoin Γ₁ Γ₂ []` forces `Γ₁ = Γ₂ = []` (`cjoin_nil`), so every
scrutinee's sub-context is again empty and the induction hypothesis applies; the
`var` leaf is VACUOUS (`[][i]? = none` refutes its lookup) — the resource-vector
mirror of "no variable in the empty context".

**Value forms of the fragment (`CValue`).** `CDeriv`'s ONLY introduction terms
are `Term.lam` (`impI`/`lolliI`) and `Term.tensorIntro` (`tensorI`); `says`/`boxed`
have NO introduction in `CDeriv` at all. So the faithful value set for this
fragment is exactly `{lam, tensorIntro}` — the restriction of `DLC.Value` to the
`CDeriv` intros. Everything else is a variable or an elimination.

**Canonical forms (inline, by syntax-directed inversion).** A `CValue` of type
`imp`/`lolli` is a `lam` (imp-β / lolli-β fire); of `tensor` is a `tensorIntro`
(tensor-E-β fires). For the modal eliminations there is NO canonical value: a
closed value of type `says`/`boxed` cannot exist in `CDeriv` (no intro), so the
scrutinee — being closed and NOT a value by inversion (`cases` on the `lam`/
`tensorIntro` derivation at a `says`/`boxed` type is vacuous) — MUST step, and the
ξ-congruence lemma lifts that step. Hence there is **no stuck term** on the
closed fragment: the modal head redexes (`saysBind`/`letSays`/`delegate`/
`discharge` on a `sign`/`boxed` scrutinee) never fire, but they never need to —
their scrutinee always ξ-steps.

**Statement.** `cprogress : CDeriv [] M ψ → CValue M ∨ ∃ M', step M = some M'`,
over ALL 11 constructors, no side condition beyond closedness `Γ = []`, no
`sorry`. Together with `cderiv_subject_reduction'` (unconditional preservation)
this is TYPE SOUNDNESS for the CARVe fragment.

Prior art (web-searched 2026-07-22): progress = "a well-typed closed term is a
value or steps", proved by induction on the typing derivation with a
canonical-forms lemma characterising well-typed closed values by type.
- PLFA, *Properties: Progress and Preservation*
  (https://plfa.github.io/Properties/ , https://plfa.inf.ed.ac.uk/Properties/):
  `Progress M = step (∃ N, M —→ N) ⊎ done (Value M)`; `Canonical V ⦂ A`
  characterises values by type (arrow → lambda); induction on `∅ ⊢ M ⦂ A`.
- Software Foundations (PLF), *StlcProp — Progress*
  (https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html): the same
  progress + canonical-forms decomposition for STLC.
- DLC's own `DLC.Progress.progress` (`lean/DLC/Progress.lean`): the
  `Value M ∨ ∃ M', step M = some M'` shape, ξ-witness lemmas, and the
  `cases scrutinee <;> first | False.elim | cases derivation` canonical-forms
  idiom this section mirrors onto `CDeriv`. -/

/-- Result `[]` forces both operands empty — the closed-context degenerate of a
`CJoin`. Lets a scrutinee under `Γ = []` inherit the empty context. -/
theorem cjoin_nil {Γ₁ Γ₂ : Carve.Ctx Prop'} (h : CJoin Γ₁ Γ₂ []) :
    Γ₁ = [] ∧ Γ₂ = [] := by
  cases h; exact ⟨rfl, rfl⟩

/-- **Values of the CARVe fragment.** `CDeriv`'s only introduction terms are
`lam` (both arrows) and `tensorIntro`; `says`/`boxed` have no intro. This is the
restriction of `DLC.Value` (`lean/DLC/Progress.lean`) to the forms `CDeriv` can
introduce — the canonical value set for progress. -/
def CValue : Term → Prop
  | Term.lam _ _ => True
  | Term.tensorIntro _ _ => True
  | _ => False

/-! ### ξ-congruence witnesses (one per `CDeriv` elimination form).
A stepping scrutinee/function position yields a step of the whole elimination.
Mirrors `DLC.Progress`'s private `*_steps` lemmas: `cases` the scrutinee — value
and head-redex shapes refute `step scrutinee = some _` (their `step` is `none`),
everything that genuinely steps falls through to `step`'s congruence branch. -/

private theorem capp_steps {f f' : Term} (x : Term)
    (hf : step f = some f') : ∃ r, step (Term.app f x) = some r := by
  cases f <;>
    first
      | (simp [step] at hf; done)
      | (refine ⟨Term.app f' x, ?_⟩; simp only [step] at hf ⊢; rw [hf])

private theorem cletTensor_steps {s s' : Term} (b : Term)
    (hs : step s = some s') : ∃ t, step (Term.letTensor s b) = some t := by
  cases s <;>
    first
      | (simp [step] at hs; done)
      | (refine ⟨Term.letTensor s' b, ?_⟩; simp only [step] at hs ⊢; rw [hs])

private theorem csaysBind_steps {p : Principal} {s s' : Term} (b : Term)
    (hs : step s = some s') : ∃ t, step (Term.saysBind p s b) = some t := by
  cases s <;>
    first
      | (simp [step] at hs; done)
      | (refine ⟨Term.saysBind p s' b, ?_⟩; simp only [step] at hs ⊢; rw [hs])

private theorem cletSays_steps {p : Principal} {s s' : Term} (b : Term)
    (hs : step s = some s') : ∃ t, step (Term.letSays p s b) = some t := by
  cases s <;>
    first
      | (simp [step] at hs; done)
      | (refine ⟨Term.letSays p s' b, ?_⟩; simp only [step] at hs ⊢; rw [hs])

private theorem cdelegate_left_steps {m m' : Term} (n : Term)
    (hm : step m = some m') : ∃ t, step (Term.delegate m n) = some t := by
  cases m <;>
    first
      | (simp [step] at hm; done)
      | (refine ⟨Term.delegate m' n, ?_⟩; simp only [step] at hm ⊢; rw [hm])

private theorem cdischarge_steps {m m' : Term} (n : Term)
    (hm : step m = some m') : ∃ t, step (Term.discharge m n) = some t := by
  cases m <;>
    first
      | (simp [step] at hm; done)
      | (refine ⟨Term.discharge m' n, ?_⟩; simp only [step] at hm ⊢; rw [hm])

/-- **Progress (auxiliary, context generalized).** Induction on the derivation:
introduction forms (`impI`/`lolliI`/`tensorI`) are `CValue`s; `var` is vacuous
under `Γ = []`; each elimination's scrutinee IH either yields a step (a ξ-witness
lifts it) or a value whose canonical form (forced by inversion of the scrutinee's
derivation) fires the head redex — and for the modal eliminations the value
branch is IMPOSSIBLE (no `says`/`boxed` value), so the scrutinee always steps. -/
private theorem cprogress_aux {Γ : Carve.Ctx Prop'} {M : Term} {ψ : Prop'}
    (d : CDeriv Γ M ψ) :
    Γ = [] → CValue M ∨ ∃ M', step M = some M' := by
  induction d with
  | @var Γ i φ m h hm hz =>
      -- No usable — in fact no — variable in the empty context.
      intro hΓ; subst hΓ; simp at h
  | impI _ _ => intro _; exact Or.inl True.intro
  | lolliI _ _ => intro _; exact Or.inl True.intro
  | tensorI _ _ _ _ _ => intro _; exact Or.inl True.intro
  | @impE Γ Γ₁ Γ₂ φ ψ f x dM dN hj hdup ihM ihN =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihM rfl with hval | ⟨f', hstep⟩
      · -- Canonical: a value of type `imp φ ψ` is a `lam` — imp-β fires.
        cases f with
        | lam _ body => exact Or.inr ⟨_, rfl⟩
        | _ => first | exact False.elim hval | cases dM
      · exact Or.inr (capp_steps x hstep)
  | @lolliE Γ Γ₁ Γ₂ φ ψ f x dM dN hj ihM ihN =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihM rfl with hval | ⟨f', hstep⟩
      · -- Canonical: a value of type `lolli φ ψ` is a `lam` — lolli-β fires.
        cases f with
        | lam _ body => exact Or.inr ⟨_, rfl⟩
        | _ => first | exact False.elim hval | cases dM
      · exact Or.inr (capp_steps x hstep)
  | @tensorE Γ Γ₁ Γ₂ φ ψ χ S B dS dB hj ihS ihB =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihS rfl with hval | ⟨S', hstep⟩
      · -- Canonical: a value of type `tensor φ ψ` is a `tensorIntro` — β fires.
        cases S with
        | tensorIntro a b => exact Or.inr ⟨_, rfl⟩
        | _ => first | exact False.elim hval | cases dS
      · exact Or.inr (cletTensor_steps B hstep)
  | @saysE Γ Γ₁ Γ₂ p φ ψ S N dS dN hj ihS ihN =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihS rfl with hval | ⟨S', hstep⟩
      · -- No closed value of type `says p φ` exists in `CDeriv` — vacuous.
        cases S <;> first | exact False.elim hval | cases dS
      · exact Or.inr (csaysBind_steps N hstep)
  | @delegate Γ Γ₁ Γ₂ p q φ m n dM dN hj ihM ihN =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihM rfl with hval | ⟨m', hstep⟩
      · -- No closed value of type `says p (q ⇒ p)` — the head never fires.
        cases m <;> first | exact False.elim hval | cases dM
      · exact Or.inr (cdelegate_left_steps n hstep)
  | @discharge Γ Γ₁ Γ₂ O φ m n dM dN hj ihM ihN =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihM rfl with hval | ⟨m', hstep⟩
      · -- No closed value of type `boxed O φ` — the head never fires.
        cases m <;> first | exact False.elim hval | cases dM
      · exact Or.inr (cdischarge_steps n hstep)
  | @letSaysE Γ Γ₁ Γ₂ p φ ψ S B dS dB hj ihS ihB =>
      intro hΓ; subst hΓ
      obtain ⟨rfl, rfl⟩ := cjoin_nil hj
      rcases ihS rfl with hval | ⟨S', hstep⟩
      · -- No closed value of type `says p φ` — the head never fires.
        cases S <;> first | exact False.elim hval | cases dS
      · exact Or.inr (cletSays_steps B hstep)

/-- **Progress for the CARVe fragment — type soundness's second half.**
A CLOSED (`Γ = []`), well-typed `CDeriv` term is a `CValue` (a `lam` or a
`tensorIntro`) or takes a deterministic `step`. Mirrors `DLC.Progress.progress`;
covers all 11 constructors with NO side condition beyond closedness and no
`sorry`. With `cderiv_subject_reduction'` (unconditional preservation) this
completes TYPE SOUNDNESS: a closed well-typed term never gets stuck. -/
theorem cprogress {M : Term} {ψ : Prop'}
    (d : CDeriv [] M ψ) : CValue M ∨ ∃ M', step M = some M' :=
  cprogress_aux d rfl

/-! ## Sanity: the CARVe split rules type real judgments with NO shift.
The multiplicative rules carry `CJoin`, not `++` + `shift` — the migration's
whole point, exercised on a concrete derivation. -/

namespace CarveJudgmentChecks

/-- `var` at position 0 of a single `many`-tagged hypothesis. The leftover
condition is VACUOUS here — there is no other position to be non-`zero`. -/
example : CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) :=
  CDeriv.var (i := 0) rfl (by decide)
    (by intro j p hj hget; rcases j with _ | k
        · exact (hj rfl).elim
        · simp at hget)

/-- A `tensorI` splitting two linear hypotheses via `CJoin` — the SAME positions,
only the tags differ, and NO `shift` appears in the conclusion. Each leaf now
witnesses the leftover condition: the OTHER `one` hypothesis is routed to the
consumed (`zero`) side of the split, so `AllZeroExcept` holds at each leaf. -/
example :
    CDeriv [(Prop'.atom 0, Mult.one), (Prop'.atom 1, Mult.one)]
      (Term.tensorIntro (Term.var 0) (Term.var 1))
      (Prop'.tensor (Prop'.atom 0) (Prop'.atom 1)) :=
  CDeriv.tensorI
    (CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | k
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget))
    (CDeriv.var (i := 1) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | k
          · simp at hget; rw [← hget]
          · exact (hj rfl).elim
          · simp at hget))
    (CJoin.cons (MJoin.zr _) (CJoin.cons (MJoin.zl _) CJoin.nil))

/-- **Anti-vacuity for additive substitution.** Substitute the closed identity
proof `λx.x : atom 0 → atom 0` (typed under the empty/`zeroed` context) for the
sole `many` hypothesis of `var 0`. The result is a REAL `CDeriv` of the same
proposition — the substitution lemma is exercised on inhabited inputs, not
vacuously on impossible ones. -/
noncomputable def substA_antivacuity_example :
    CDeriv [] (Term.lam (Prop'.atom 0) (Term.var 0))
      (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) := by
  have dN : CDeriv (zeroed ([] : Carve.Ctx Prop'))
      (Term.lam (Prop'.atom 0) (Term.var 0))
      (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.impI (CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget))
  have dM : CDeriv ([] ++ (Prop'.imp (Prop'.atom 0) (Prop'.atom 0), Mult.many) :: [])
      (Term.var 0) (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget)
  exact cderiv_substA (Γl := []) (Γr := []) dM dN

/-- **Anti-vacuity for LINEAR substitution.** Substitute `N = var 0`, which
CONSUMES a genuine linear resource (`Δ = [(atom 0, one)]`), for the linear
(`Mult.one`) hypothesis at position 0 of `M = var 0` — whose context also
carries an unused `(atom 0, zero)` leftover slot `Γr`. `N`'s LIVE resource is
`CJoin`-MERGED into that slot (`MJoin zero one one`), so the result is a REAL
`CDeriv` still carrying the merged `(atom 0, one)`: the linear-substitution
lemma is exercised with genuinely non-vanishing resources, not vacuously. -/
noncomputable def substL_antivacuity_example :
    CDeriv [(Prop'.atom 0, Mult.one)] (Term.var 0) (Prop'.atom 0) := by
  have dM : CDeriv ([] ++ (Prop'.atom 0, Mult.one) :: [(Prop'.atom 0, Mult.zero)])
      (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | k
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget)
  have dN : CDeriv [(Prop'.atom 0, Mult.one)] (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget)
  have hc : CJoin [(Prop'.atom 0, Mult.zero)] [(Prop'.atom 0, Mult.one)]
      [(Prop'.atom 0, Mult.one)] :=
    CJoin.cons (MJoin.zl _) CJoin.nil
  exact cderiv_substL (Γl := []) (Γr := [(Prop'.atom 0, Mult.zero)]) dM dN hc

/-- **Anti-vacuity for OPEN ADDITIVE (scaled) substitution.** Substitute
`N = var 0`, carrying its OWN OPEN resource `Δ = [(atom 0, many)]` (a genuine,
non-`zeroed` context that is nonetheless DUPLICABLE — `NoOne` holds since the
tag is `many`, not `one`), for the ADDITIVE (`Mult.many`) hypothesis at position
0 of `M = var 0`, whose context also carries an unused `(atom 0, zero)` leftover
slot `Γr`. `N`'s live `many` resource is `CJoin`-MERGED into that slot
(`MJoin zero many many`), so the result is a REAL `CDeriv` still carrying the
merged `(atom 0, many)`: the scaled-substitution lemma is exercised with a
genuinely OPEN, non-vanishing (and correctly duplicable) `Δ`, not vacuously. -/
noncomputable def substM_antivacuity_example :
    CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) := by
  have dM : CDeriv ([] ++ (Prop'.atom 0, Mult.many) :: [(Prop'.atom 0, Mult.zero)])
      (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | k
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget)
  have dN : CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget)
  have hdup : NoOne [(Prop'.atom 0, Mult.many)] := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; decide
  have hc : CJoin [(Prop'.atom 0, Mult.zero)] [(Prop'.atom 0, Mult.many)]
      [(Prop'.atom 0, Mult.many)] :=
    CJoin.cons (MJoin.zl _) CJoin.nil
  exact cderiv_substM (Γl := []) (Γr := [(Prop'.atom 0, Mult.zero)]) dM dN hdup hc

/-- **Anti-vacuity for subject reduction (tightened `⊃` imp-β path).** A REAL,
inhabited CDeriv-typed redex `(λ^many x:atom0. x) (var 0)` under
`Γ = [(atom0, many)]`, where the argument's context `[(atom0, many)]` is
DUPLICABLE (satisfies the tightened `impE`'s `NoOne` side condition), which
`step`s to `var 0`, and the UNCONDITIONAL `cderiv_subject_reduction'` delivers
the REDUCED derivation `CDeriv Γ (var 0) atom0`. Exercises the imp-β case through
the tightened `impE` + `cderiv_imp_beta`/`cderiv_substM` on non-vacuous inputs
(the argument `var 0` genuinely consumes the ambient `many` hypothesis). -/
noncomputable def subjectReduction_impBeta_example :
    CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) := by
  have dN : CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget)
  have dLam : CDeriv [(Prop'.atom 0, Mult.zero)]
      (Term.lam (Prop'.atom 0) (Term.var 0))
      (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.impI (CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | k
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget))
  have hj : CJoin [(Prop'.atom 0, Mult.zero)] [(Prop'.atom 0, Mult.many)]
      [(Prop'.atom 0, Mult.many)] := CJoin.cons (MJoin.zl _) CJoin.nil
  -- The tightened `impE` demands the argument's context be duplicable — here `many`.
  have hdup : NoOne [(Prop'.atom 0, Mult.many)] := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; decide
  have dApp : CDeriv [(Prop'.atom 0, Mult.many)]
      (Term.app (Term.lam (Prop'.atom 0) (Term.var 0)) (Term.var 0))
      (Prop'.atom 0) := CDeriv.impE dLam dN hj hdup
  exact cderiv_subject_reduction' dApp (Term.var 0) rfl

/-- **Anti-vacuity + the `⊸`-β CONTRAST (bite b).** A REAL, inhabited redex
`(λ^one x:atom0. x) (var 0)` typed at the LINEAR arrow `atom0 ⊸ atom0` (via
`lolliI`/`lolliE`) under `Γ = [(atom0, one)]` — the argument carries a LIVE
LINEAR (`one`) resource, which `⊃` would REJECT (its tightened `impE` needs a
duplicable argument) but `⊸` accepts UNCONDITIONALLY. `step`s to `var 0`, and the
UNCONDITIONAL `cderiv_subject_reduction'` delivers the reduced derivation with NO
`NoOne` side condition — the linear cut `cderiv_substL` merges the argument's
resource without duplication. This is the exact contrast to the tightened-`⊃`
example above: same term shape, but a linear argument is sound at `⊸`, unsound
at `⊃`. -/
noncomputable def subjectReduction_lolliBeta_example :
    CDeriv [(Prop'.atom 0, Mult.one)] (Term.var 0) (Prop'.atom 0) := by
  have dN : CDeriv [(Prop'.atom 0, Mult.one)] (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget)
  have dLam : CDeriv [(Prop'.atom 0, Mult.zero)]
      (Term.lam (Prop'.atom 0) (Term.var 0))
      (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.lolliI (CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | k
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget))
  have hj : CJoin [(Prop'.atom 0, Mult.zero)] [(Prop'.atom 0, Mult.one)]
      [(Prop'.atom 0, Mult.one)] := CJoin.cons (MJoin.zl _) CJoin.nil
  -- No `NoOne` needed — `lolliE` takes an arbitrary (here linear) argument.
  have dApp : CDeriv [(Prop'.atom 0, Mult.one)]
      (Term.app (Term.lam (Prop'.atom 0) (Term.var 0)) (Term.var 0))
      (Prop'.atom 0) := CDeriv.lolliE dLam dN hj
  exact cderiv_subject_reduction' dApp (Term.var 0) rfl

/-- **Anti-vacuity for subject reduction (the LINEAR load-bearing tensor-β).**
A REAL redex `let x⊗y = (var 0 ⊗ var 0) in (x ⊗ y)` under `Γ = [(atom0, many)]`
(`NoOne Γ`), which `step`s to `subst (subst (var 0 ⊗ var 1) (shift (var 0) 1 0))
(var 0)`, and `cderiv_subject_reduction` delivers the reduced derivation.
Exercises the tensor-E-β path (two `cderiv_substL`, `cderiv_shift`,
`cjoin_reassoc`) on genuinely LINEAR binders. -/
noncomputable def subjectReduction_tensorBeta_example :
    CDeriv [(Prop'.atom 0, Mult.many)]
      (Term.tensorIntro (Term.var 0) (Term.var 0))
      (Prop'.tensor (Prop'.atom 0) (Prop'.atom 0)) := by
  -- scrutinee `var 0 ⊗ var 0 : atom0 ⊗ atom0`, both halves consuming the ambient `many`.
  have dSa : CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget)
  have dS : CDeriv [(Prop'.atom 0, Mult.many)]
      (Term.tensorIntro (Term.var 0) (Term.var 0))
      (Prop'.tensor (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.tensorI dSa dSa (CJoin.cons MJoin.mm CJoin.nil)
  -- body `x ⊗ y : atom0 ⊗ atom0` over the two `one` binders (+ a spent `zero` slot).
  have dBx : CDeriv [(Prop'.atom 0, Mult.one), (Prop'.atom 0, Mult.zero),
      (Prop'.atom 0, Mult.zero)] (Term.var 0) (Prop'.atom 0) :=
    CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | _ | k
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget; rw [← hget]
          · simp at hget)
  have dBy : CDeriv [(Prop'.atom 0, Mult.zero), (Prop'.atom 0, Mult.one),
      (Prop'.atom 0, Mult.zero)] (Term.var 1) (Prop'.atom 0) :=
    CDeriv.var (i := 1) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | _ | _ | k
          · simp at hget; rw [← hget]
          · exact (hj rfl).elim
          · simp at hget; rw [← hget]
          · simp at hget)
  have dB : CDeriv [(Prop'.atom 0, Mult.one), (Prop'.atom 0, Mult.one),
      (Prop'.atom 0, Mult.zero)] (Term.tensorIntro (Term.var 0) (Term.var 1))
      (Prop'.tensor (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.tensorI dBx dBy
      (CJoin.cons (MJoin.zr _) (CJoin.cons (MJoin.zl _) (CJoin.cons (MJoin.zl _) CJoin.nil)))
  have hj : CJoin [(Prop'.atom 0, Mult.many)] [(Prop'.atom 0, Mult.zero)]
      [(Prop'.atom 0, Mult.many)] := CJoin.cons (MJoin.zr _) CJoin.nil
  have dLet : CDeriv [(Prop'.atom 0, Mult.many)]
      (Term.letTensor (Term.tensorIntro (Term.var 0) (Term.var 0))
        (Term.tensorIntro (Term.var 0) (Term.var 1)))
      (Prop'.tensor (Prop'.atom 0) (Prop'.atom 0)) :=
    CDeriv.tensorE dS dB hj
  have hΓ : NoOne [(Prop'.atom 0, Mult.many)] := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; decide
  exact cderiv_subject_reduction dLet hΓ (Term.tensorIntro (Term.var 0) (Term.var 0)) rfl

/-! ### Anti-vacuity for progress (`cprogress`).
Two real, CLOSED (`Γ = []`), inhabited `CDeriv`s: a non-value REDEX that
`cprogress` shows STEPS, and a VALUE where `cprogress` gives the value branch
(stepping being impossible). Both exercise `cprogress` on genuine inputs. -/

/-- A closed identity `λx:atom0. x` at the LINEAR arrow `atom0 ⊸ atom0` — a
`CValue` normal form (`step = none`). -/
noncomputable def progress_val_deriv :
    CDeriv [] (Term.lam (Prop'.atom 0) (Term.var 0))
      (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) :=
  CDeriv.lolliI (CDeriv.var (i := 0) rfl (by decide)
    (by intro j p hj hget; rcases j with _ | k
        · exact (hj rfl).elim
        · simp at hget))

/-- A closed REDEX `(λf:(atom0⊸atom0). f) (λx:atom0. x)` at `atom0 ⊸ atom0`,
built with `lolliE` over `CJoin [] [] []` — a non-value that `step`s (imp/lolli-β
fires: `→ subst (var 0) (λx.x) = λx.x`). -/
noncomputable def progress_redex_deriv :
    CDeriv []
      (Term.app
        (Term.lam (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) (Term.var 0))
        (Term.lam (Prop'.atom 0) (Term.var 0)))
      (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) := by
  have dFun : CDeriv []
      (Term.lam (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) (Term.var 0))
      (Prop'.lolli (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0))
        (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0))) :=
    CDeriv.lolliI (CDeriv.var (i := 0) rfl (by decide)
      (by intro j p hj hget; rcases j with _ | k
          · exact (hj rfl).elim
          · simp at hget))
  exact CDeriv.lolliE dFun progress_val_deriv CJoin.nil

/-- **The REDEX genuinely steps, and `cprogress` returns the step branch.** The
right disjunct is extracted from `cprogress` applied to a real derivation, and the
reduct is exhibited by `rfl` — non-vacuous. -/
example : ∃ M', step
    (Term.app
      (Term.lam (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) (Term.var 0))
      (Term.lam (Prop'.atom 0) (Term.var 0))) = some M' := by
  rcases cprogress progress_redex_deriv with hval | hstep
  · exact absurd hval (by simp [CValue])  -- a redex `app …` is not a `CValue`
  · exact hstep

/-- The redex reduces to the identity `λx.x` (the concrete reduct). -/
example : step
    (Term.app
      (Term.lam (Prop'.lolli (Prop'.atom 0) (Prop'.atom 0)) (Term.var 0))
      (Term.lam (Prop'.atom 0) (Term.var 0)))
    = some (Term.lam (Prop'.atom 0) (Term.var 0)) := rfl

/-- **The VALUE cannot step, so `cprogress` returns the value branch.** Extracting
the left disjunct from `cprogress` on the real value derivation (the right is
refuted by `step = none`) — non-vacuous. -/
example : CValue (Term.lam (Prop'.atom 0) (Term.var 0)) := by
  rcases cprogress progress_val_deriv with hval | ⟨M', hM'⟩
  · exact hval
  · simp [step] at hM'  -- `step (lam …) = none`, so the step branch is impossible

end CarveJudgmentChecks

end DLC
