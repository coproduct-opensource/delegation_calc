import DLC.Subst
import DLC.CarveCtx

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
  /-- `imp-E` (`app`) — the context JOINS; no shift in the conclusion. -/
  | impE {Γ Γ₁ Γ₂ : Carve.Ctx Prop'} {φ ψ : Prop'} {M N : Term}
      (dM : CDeriv Γ₁ M (Prop'.imp φ ψ)) (dN : CDeriv Γ₂ N φ)
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
  | impE _dM _dN hj ihM ihN =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact CDeriv.impE (by rw [← hn1]; exact ihM Γl₁ Γm Γr₁ rfl)
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
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne _ _ hj ihM ihN =>
      intro Γl Γr m hΓ hm dN
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ := cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hm1, hm2⟩ := mjoin_ne_one hmj hm
      unfold substAt
      have hM := ihM Γl₁ Γr₁ m₁ rfl hm1 (by rw [cjoin_zeroed_left hjr]; exact dN)
      have hN := ihN Γl₂ Γr₂ m₂ rfl hm2 (by rw [cjoin_zeroed_right hjr]; exact dN)
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.impE hM hN (cjoin_append hjl hjr)
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
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne _ _ hj ihM ihN =>
      intro Γl Γr hΓ; subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, m₁, m₂, e1, e2, hn1, hn2, hmj, hjl, hjr⟩ :=
        cjoin_split_cons hj
      subst e1; subst e2
      obtain ⟨hz1, hz2⟩ := mjoin_zero hmj; subst hz1; subst hz2
      unfold substAt
      have hM := ihM Γl₁ Γr₁ rfl; have hN := ihN Γl₂ Γr₂ rfl
      rw [hn1] at hM; rw [hn2] at hN
      exact CDeriv.impE hM hN (cjoin_append hjl hjr)
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
  | @impE Γ Γ₁ Γ₂ φe ψe Me Ne dMe dNe hj ihM ihN =>
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
          exact CDeriv.impE hM hN (cjoin_append hjl hADBr)
      ·
          obtain ⟨hm1z, hm2o⟩ := mjoin_one_notleft hmj hone
          subst hm1z; subst hm2o
          obtain ⟨Δr, hADr, hADBr⟩ := cjoin_reassoc (cjoin_comm hjr) hc
          have hM := cderiv_dropZero_aux φ N dMe Γl₁ Γr₁ rfl
          have hN := ihN Γl₂ Γr₂ Δ Δr rfl dN hADr
          rw [hn1] at hM; rw [hn2] at hN
          exact CDeriv.impE hM hN (cjoin_append hjl (cjoin_comm hADBr))
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

end CarveJudgmentChecks

end DLC
