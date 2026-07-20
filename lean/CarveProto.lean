/-! # CARVe-representation validation prototype

Scope: does L3a's `tensorE` case go through when contexts are single
resource-tagged vectors that are JOINED elementwise rather than SPLIT by
`++`? This is the claim option (c) rests on. Self-contained on purpose --
it imports nothing from `DLC` so it can be judged on its own.

What is modelled: the INDEXING discipline (positions, binders, shift,
weakening-in-the-middle) and elementwise joins.
What is deliberately NOT modelled: the linear-usage side condition on the
variable rule (that every OTHER linear position is consumed). That is a
soundness condition, not an indexing one, and it is orthogonal to the
question being tested. See the note at the bottom.
-/

namespace CarveProto

/-- Multiplicity tags. `zero` = consumed/absent, `one` = linear,
`many` = unrestricted (the additive hypotheses of the current `Ctx`). -/
inductive Mult | zero | one | many
  deriving DecidableEq, Repr

/-- The resource algebra's partial join, as a relation. -/
inductive MJoin : Mult → Mult → Mult → Prop
  | zl (m : Mult) : MJoin Mult.zero m m
  | zr (m : Mult) : MJoin m Mult.zero m
  | mm : MJoin Mult.many Mult.many Mult.many

inductive Ty | atom (n : Nat) | arrow (a b : Ty) | tensor (a b : Ty)
  deriving DecidableEq, Repr

/-- A context is ONE vector of tagged hypotheses. It is never restructured. -/
abbrev Ctx := List (Ty × Mult)

/-- Elementwise join. Note both operands and the result have the SAME
length and the SAME types at every position -- only tags differ. This is
the entire point: a "split" never moves an index. -/
inductive CJoin : Ctx → Ctx → Ctx → Type
  | nil : CJoin [] [] []
  | cons {a : Ty} {m₁ m₂ m : Mult} {Γ₁ Γ₂ Γ : Ctx} :
      MJoin m₁ m₂ m → CJoin Γ₁ Γ₂ Γ →
      CJoin ((a, m₁) :: Γ₁) ((a, m₂) :: Γ₂) ((a, m) :: Γ)

inductive Tm
  | var (i : Nat)
  | lam (b : Tm)
  | app (f x : Tm)
  | tenI (m n : Tm)
  | letT (s b : Tm)
  deriving Repr

def shift : Tm → Nat → Nat → Tm
  | Tm.var i,    d, c => if i < c then Tm.var i else Tm.var (i + d)
  | Tm.lam b,    d, c => Tm.lam (shift b d (c + 1))
  | Tm.app f x,  d, c => Tm.app (shift f d c) (shift x d c)
  | Tm.tenI m n, d, c => Tm.tenI (shift m d c) (shift n d c)
  | Tm.letT s b, d, c => Tm.letT (shift s d c) (shift b d (c + 2))

/-- The judgment. Every elimination rule JOINS instead of splitting, so --
unlike the current `Deriv` -- **no rule carries a `shift` in its
conclusion**. -/
inductive D : Ctx → Tm → Ty → Type
  | var {Γ : Ctx} {i : Nat} {a : Ty} {m : Mult}
      (h : Γ[i]? = some (a, m)) (hm : m ≠ Mult.zero) :
      D Γ (Tm.var i) a
  | lam {Γ : Ctx} {a b : Ty} {body : Tm}
      (d : D ((a, Mult.many) :: Γ) body b) :
      D Γ (Tm.lam body) (Ty.arrow a b)
  | app {Γ Γ₁ Γ₂ : Ctx} {a b : Ty} {f x : Tm}
      (df : D Γ₁ f (Ty.arrow a b)) (dx : D Γ₂ x a) (hj : CJoin Γ₁ Γ₂ Γ) :
      D Γ (Tm.app f x) b
  | tenI {Γ Γ₁ Γ₂ : Ctx} {a b : Ty} {m n : Tm}
      (dm : D Γ₁ m a) (dn : D Γ₂ n b) (hj : CJoin Γ₁ Γ₂ Γ) :
      D Γ (Tm.tenI m n) (Ty.tensor a b)
  /-- The rule that currently resists. Its two binders are LINEAR (`one`)
  and they extend the context by two, so they occupy two real de Bruijn
  slots -- which is exactly what `shift`'s `c + 2` assumes. -/
  | letT {Γ Γ₁ Γ₂ : Ctx} {a b c : Ty} {s body : Tm}
      (ds : D Γ₁ s (Ty.tensor a b))
      (db : D ((a, Mult.one) :: (b, Mult.one) :: Γ₂) body c)
      (hj : CJoin Γ₁ Γ₂ Γ) :
      D Γ (Tm.letT s body) c

/-- Weakening material: the inserted block, tagged `zero` (present but
unused), which is what makes it joinable with itself. -/
def zeroed (Γm : Ctx) : Ctx := Γm.map (fun p => (p.1, Mult.zero))

theorem zeroed_length (Γm : Ctx) : (zeroed Γm).length = Γm.length := by
  simp [zeroed]

/-- `zeroed Γm` joins with itself to give `zeroed Γm`: unused stays unused. -/
noncomputable def cjoin_zeroed (Γm : Ctx) : CJoin (zeroed Γm) (zeroed Γm) (zeroed Γm) := by
  induction Γm with
  | nil => exact CJoin.nil
  | cons p Γ ih => exact CJoin.cons (MJoin.zl _) ih

/-- The result of splitting a join at a common prefix length. A structure
rather than an `∃` because `D` is `Type`-valued and must consume it. -/
structure SplitAt (Γ₁ Γ₂ Γl Γr : Ctx) : Type where
  Γl₁ : Ctx
  Γr₁ : Ctx
  Γl₂ : Ctx
  Γr₂ : Ctx
  e₁ : Γ₁ = Γl₁ ++ Γr₁
  e₂ : Γ₂ = Γl₂ ++ Γr₂
  n₁ : Γl₁.length = Γl.length
  n₂ : Γl₂.length = Γl.length
  jl : CJoin Γl₁ Γl₂ Γl
  jr : CJoin Γr₁ Γr₂ Γr

/-- Splitting a join at a common prefix length. This is the ONLY structural
fact the induction needs about joins, and it holds because joins preserve
positions -- it partitions TAGS and moves no index. -/
noncomputable def cjoin_split : ∀ {Γ₁ Γ₂ : Ctx} (Γl Γr : Ctx), CJoin Γ₁ Γ₂ (Γl ++ Γr) →
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

/-- Re-assembling a join after inserting the SAME zeroed block into both
operands and the result. -/
noncomputable def cjoin_insert {Γl₁ Γr₁ Γl₂ Γr₂ Γl Γr Γm : Ctx}
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

/-- **The validation.** Weakening-in-the-middle over the CARVe
representation, INCLUDING the `letT` case that currently resists. -/
noncomputable def d_shift {Γfull : Ctx} {M : Tm} {A : Ty} (d : D Γfull M A) :
    ∀ (Γl Γm Γr : Ctx), Γfull = Γl ++ Γr →
      D (Γl ++ zeroed Γm ++ Γr) (shift M Γm.length Γl.length) A := by
  induction d with
  | @var Γ i a m h hm =>
      intro Γl Γm Γr hΓ
      subst hΓ
      simp only [shift]
      by_cases hcut : i < Γl.length
      · rw [if_pos hcut]
        refine D.var (m := m) ?_ hm
        rw [List.getElem?_append_left (by simp [zeroed_length]; omega),
            List.getElem?_append_left hcut]
        rwa [List.getElem?_append_left hcut] at h
      · rw [if_neg hcut]
        refine D.var (m := m) ?_ hm
        rw [List.getElem?_append_right (by simp [zeroed_length]; omega),
            show i + Γm.length - (Γl ++ zeroed Γm).length = i - Γl.length from by
              simp [zeroed_length]; omega]
        rwa [List.getElem?_append_right (by omega)] at h
  | lam _d ih =>
      intro Γl Γm Γr hΓ
      subst hΓ
      simp only [shift]
      exact D.lam (by simpa using ih (_ :: Γl) Γm Γr rfl)
  | app _df _dx hj ihf ihx =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact D.app (by rw [← hn1]; exact ihf Γl₁ Γm Γr₁ rfl)
                  (by rw [← hn2]; exact ihx Γl₂ Γm Γr₂ rfl)
                  (cjoin_insert hjl hjr)
  | tenI _dm _dn hj ihm ihn =>
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      exact D.tenI (by rw [← hn1]; exact ihm Γl₁ Γm Γr₁ rfl)
                   (by rw [← hn2]; exact ihn Γl₂ Γm Γr₂ rfl)
                   (cjoin_insert hjl hjr)
  | letT _ds _db hj ihs ihb =>
      -- THE CASE THAT CURRENTLY RESISTS.
      intro Γl Γm Γr hΓ
      subst hΓ
      obtain ⟨Γl₁, Γr₁, Γl₂, Γr₂, h1, h2, hn1, hn2, hjl, hjr⟩ := cjoin_split Γl Γr hj
      subst h1; subst h2
      simp only [shift]
      refine D.letT (by rw [← hn1]; exact ihs Γl₁ Γm Γr₁ rfl) ?_
        (cjoin_insert hjl hjr)
      -- The two LINEAR binders extend the context by two, so the body's
      -- insertion point is |Γl| + 2 -- matching `shift`'s `c + 2` exactly.
      have h := ihb (_ :: _ :: Γl₂) Γm Γr₂ rfl
      simpa [hn2, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-! ## Result

`d_shift` compiles. In particular the `letT` case closes with the IH taken
at `Γl₂` extended by the two binders, and the resulting cutoff `|Γl| + 2`
matches `shift`'s `letT` clause on the nose.

Two things did NOT appear anywhere in this proof:

* **no shift-commutation lemma** (`shift_shift_comm`) -- because no rule
  carries a shift in its conclusion; and
* **no re-indexing after a split** -- `cjoin_split` moves no index, it only
  partitions tags.

Both are direct consequences of joins preserving position, and both are the
costs the current `{additive, linear}` representation pays on every rule.

CAVEAT, stated so it is not overclaimed: the linear-usage side condition on
`D.var` is omitted (see the header). Adding it requires that the inserted
block be `zero`-tagged -- which `zeroed` already guarantees -- so it is
expected to go through, but this prototype does not prove that.
-/

end CarveProto
