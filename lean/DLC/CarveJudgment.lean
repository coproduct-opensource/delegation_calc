import DLC.Subst
import DLC.CarveCtx

/-! # CARVe-migrated judgment — real `Term`/`Prop'` fragment + weakening-in-the-middle
     (DLC-D Phase 0, increment 1)

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

## Scope of this increment (honest)
A REPRESENTATIVE fragment — `var`, `lam`(imp-I), `app`(imp-E), `tensorIntro`,
`letTensor`(tensor-E) — exercising the two var multiplicities and the
multiplicative `CJoin` split. As in `CarveProto`, the linear-usage side
condition on `CDeriv.var` (every OTHER `one` position is consumed) is an
orthogonal SOUNDNESS condition, not an INDEXING one, and is omitted here;
`zeroed` already `zero`-tags the inserted block, so adding it is expected to
go through. The full-judgment migration + the `one`-usage side condition +
substitution (L4) are subsequent increments.
-/

namespace DLC

open DLC.Carve (Mult MJoin CJoin zeroed zeroed_length cjoin_split cjoin_insert)

/-- The CARVe-migrated derivation, on the real `Term`/`Prop'`, over a resource-
vector context `DLC.Carve.Ctx Prop' = List (Prop' × Mult)`. Every elimination
rule JOINS (`CJoin`) instead of splitting `Γ₁ ++ Γ₂`, so — unlike `DLC.Deriv` —
**no constructor carries a `shift` in its conclusion**. -/
inductive CDeriv : Carve.Ctx Prop' → Term → Prop' → Type where
  /-- `var` — position lookup; the used hypothesis is non-`zero`. (The
  linear-usage side condition on the OTHER positions is omitted per the header.) -/
  | var {Γ : Carve.Ctx Prop'} {i : Nat} {φ : Prop'} {m : Mult}
      (h : Γ[i]? = some (φ, m)) (hm : m ≠ Mult.zero) :
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
  | @var Γ i φ m h hm =>
      intro Γl Γm Γr hΓ
      subst hΓ
      simp only [shift]
      by_cases hcut : i < Γl.length
      · rw [if_pos hcut]
        refine CDeriv.var (m := m) ?_ hm
        rw [List.getElem?_append_left (by simp [zeroed_length]; omega),
            List.getElem?_append_left hcut]
        rwa [List.getElem?_append_left hcut] at h
      · rw [if_neg hcut]
        refine CDeriv.var (m := m) ?_ hm
        rw [List.getElem?_append_right (by simp [zeroed_length]; omega),
            show i + Γm.length - (Γl ++ zeroed Γm).length = i - Γl.length from by
              simp [zeroed_length]; omega]
        rwa [List.getElem?_append_right (by omega)] at h
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

/-! ## Sanity: the CARVe split rules type real judgments with NO shift.
The multiplicative rules carry `CJoin`, not `++` + `shift` — the migration's
whole point, exercised on a concrete derivation. -/

namespace CarveJudgmentChecks

/-- `var` at position 0 of a single `many`-tagged hypothesis. -/
example : CDeriv [(Prop'.atom 0, Mult.many)] (Term.var 0) (Prop'.atom 0) :=
  CDeriv.var (i := 0) rfl (by decide)

/-- A `tensorI` splitting two linear hypotheses via `CJoin` — the SAME positions,
only the tags differ, and NO `shift` appears in the conclusion. -/
example :
    CDeriv [(Prop'.atom 0, Mult.one), (Prop'.atom 1, Mult.one)]
      (Term.tensorIntro (Term.var 0) (Term.var 1))
      (Prop'.tensor (Prop'.atom 0) (Prop'.atom 1)) :=
  CDeriv.tensorI
    (CDeriv.var (i := 0) rfl (by decide))
    (CDeriv.var (i := 1) rfl (by decide))
    (CJoin.cons (MJoin.zr _) (CJoin.cons (MJoin.zl _) CJoin.nil))

end CarveJudgmentChecks

end DLC
