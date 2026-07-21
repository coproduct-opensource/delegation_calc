/-! # Resource-vector contexts (CARVe) — production foundation

The context representation for the L3/L4 migration
(`spec/carve-context-design-2026-07.md`). A context is ONE vector of
hypotheses, each tagged with a multiplicity from a resource algebra, and it
is **never restructured**: a "split" becomes an elementwise join of the tag
vectors at the *same* length, so positions and de Bruijn indices are
preserved automatically.

This module holds only the context machinery — `Mult`, `CJoin`, and the
three structural lemmas any substructural judgment over these contexts needs
(`cjoin_split`, `cjoin_insert`, `cjoin_zeroed`). It is generic over the entry
type `α`; the judgment migration instantiates `α := Prop'`.

The design and its machine-checked validation are in `lean/CarveProto.lean`
(a self-contained miniature calculus that proves weakening-in-the-middle,
including the `tensorE`-shaped case that the current `{additive, linear}`
representation cannot). Everything here is the same infrastructure promoted
off the toy entry type onto an arbitrary `α`; `CarveProto` can retire once
the migration lands.

`CJoin` is `Type`-valued (not `Prop`) because `Deriv` is `Type`-valued and
must eliminate a split into it — the lesson from the prototype.
-/

namespace DLC.Carve

/-- Multiplicity tags. `zero` = consumed/absent, `one` = linear (use exactly
once), `many` = unrestricted (the additive hypotheses). -/
inductive Mult | zero | one | many
  deriving DecidableEq, Repr

/-- The resource algebra's partial join, as a relation: `zero` is the unit,
and only `many` is idempotent (a linear `one` cannot be shared). -/
inductive MJoin : Mult → Mult → Mult → Prop
  | zl (m : Mult) : MJoin Mult.zero m m
  | zr (m : Mult) : MJoin m Mult.zero m
  | mm : MJoin Mult.many Mult.many Mult.many

/-- A context: one vector of tagged hypotheses, never restructured. -/
abbrev Ctx (α : Type) := List (α × Mult)

/-- Elementwise join. Both operands and the result share length and share the
entry at every position — only the tags differ. That is the whole point: a
"split" moves no index. -/
inductive CJoin {α : Type} : Ctx α → Ctx α → Ctx α → Type
  | nil : CJoin [] [] []
  | cons {a : α} {m₁ m₂ m : Mult} {Γ₁ Γ₂ Γ : Ctx α} :
      MJoin m₁ m₂ m → CJoin Γ₁ Γ₂ Γ →
      CJoin ((a, m₁) :: Γ₁) ((a, m₂) :: Γ₂) ((a, m) :: Γ)

/-- The weakening block: a context with every tag set to `zero` (present but
unused), which is what makes it joinable with itself. -/
def zeroed {α : Type} (Γm : Ctx α) : Ctx α := Γm.map (fun p => (p.1, Mult.zero))

@[simp] theorem zeroed_length {α : Type} (Γm : Ctx α) :
    (zeroed Γm).length = Γm.length := by simp [zeroed]

/-- `zeroed Γm` joins with itself to give `zeroed Γm`: unused stays unused. -/
noncomputable def cjoin_zeroed {α : Type} (Γm : Ctx α) :
    CJoin (zeroed Γm) (zeroed Γm) (zeroed Γm) := by
  induction Γm with
  | nil => exact CJoin.nil
  | cons p Γ ih => exact CJoin.cons (MJoin.zl _) ih

/-- The result of splitting a join at a common prefix length. A structure
(not an `∃`) because a `Type`-valued judgment must consume it. -/
structure SplitAt {α : Type} (Γ₁ Γ₂ Γl Γr : Ctx α) : Type where
  Γl₁ : Ctx α
  Γr₁ : Ctx α
  Γl₂ : Ctx α
  Γr₂ : Ctx α
  e₁ : Γ₁ = Γl₁ ++ Γr₁
  e₂ : Γ₂ = Γl₂ ++ Γr₂
  n₁ : Γl₁.length = Γl.length
  n₂ : Γl₂.length = Γl.length
  jl : CJoin Γl₁ Γl₂ Γl
  jr : CJoin Γr₁ Γr₂ Γr

/-- **Split a join at a common prefix length.** The only structural fact a
weakening/substitution induction needs about joins, and it holds because
joins preserve positions — it partitions TAGS and moves no index. This is
what makes the split rules carry no shift in their conclusions. -/
noncomputable def cjoin_split {α : Type} :
    ∀ {Γ₁ Γ₂ : Ctx α} (Γl Γr : Ctx α), CJoin Γ₁ Γ₂ (Γl ++ Γr) →
      SplitAt Γ₁ Γ₂ Γl Γr := by
  intro Γ₁ Γ₂ Γl
  induction Γl generalizing Γ₁ Γ₂ with
  | nil =>
      intro Γr hj
      exact ⟨[], Γ₁, [], Γ₂, rfl, rfl, rfl, rfl, CJoin.nil, by simpa using hj⟩
  | cons p Γl' ih =>
      intro Γr hj
      cases hj with
      | cons hm hrest =>
          let r := ih Γr hrest
          exact ⟨_ :: r.Γl₁, r.Γr₁, _ :: r.Γl₂, r.Γr₂,
                 by simp [r.e₁], by simp [r.e₂],
                 by simp [r.n₁], by simp [r.n₂],
                 CJoin.cons hm r.jl, r.jr⟩

/-- **Re-assemble a join after inserting the same zeroed block** into both
operands and the result — the join-side counterpart of shifting a derivation
by a middle-inserted block of hypotheses. -/
noncomputable def cjoin_insert {α : Type} {Γl₁ Γr₁ Γl₂ Γr₂ Γl Γr Γm : Ctx α}
    (hl : CJoin Γl₁ Γl₂ Γl) (hr : CJoin Γr₁ Γr₂ Γr) :
    CJoin (Γl₁ ++ zeroed Γm ++ Γr₁) (Γl₂ ++ zeroed Γm ++ Γr₂)
          (Γl ++ zeroed Γm ++ Γr) := by
  induction hl with
  | nil =>
      simpa using
        (by
          induction Γm with
          | nil => simpa using hr
          | cons p Γ ih => exact CJoin.cons (MJoin.zl _) ih :
          CJoin (zeroed Γm ++ Γr₁) (zeroed Γm ++ Γr₂) (zeroed Γm ++ Γr))
  | cons hm _ ih => exact CJoin.cons hm ih

/-! ## Regressions — the two properties that make the representation work.

If either stops holding, the migration's foundation is broken. Kept as
theorems so a future edit cannot silently weaken them. -/

/-- Joins preserve length (both operands and the result agree). This is the
"positions never move" invariant stated directly. -/
theorem cjoin_length {α : Type} {Γ₁ Γ₂ Γ : Ctx α} (h : CJoin Γ₁ Γ₂ Γ) :
    Γ₁.length = Γ.length ∧ Γ₂.length = Γ.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- A `one` (linear) tag is NOT idempotent under the join: there is no way to
route a linear hypothesis into both halves of a split. This is the algebraic
fact that enforces "use exactly once". -/
theorem mjoin_one_not_shared : ¬ MJoin Mult.one Mult.one Mult.one := by
  intro h; cases h

end DLC.Carve
