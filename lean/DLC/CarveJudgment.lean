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

end CarveJudgmentChecks

end DLC
