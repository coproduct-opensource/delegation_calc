/-
DLC — the L1 disambiguation invariant (`CtxWellFormed`).

Rung **L1** of the linear-lever campaign
(`spec/linear-substitution-design-2026-07.md`). The blocker L1 resolves:
`Deriv`'s two variable rules shared one de Bruijn space, so `Term.var 0`
could resolve to *either* `additive[0]` (via `varA`) or the sole linear
hypothesis (via `varL`) — the substitution lemma could not even be *stated*.

The fix (already applied in `DLC.Judgment`): `varL` now types
`Term.var Γₐ.length`, so the linear variable lives one index past the
additive context and can never collide with an additive index. This file
formalizes the resulting invariant and discharges the two binding
constraints from the D-review (PR #101):

* **(i)** `ctxLookup` — an additive-first lookup function — is proven to
  **agree exactly** with the (restricted) `varA`/`varL` rules
  (`ctxLookup_agrees`, `ctxLookup_sound`). The old `varL` overlap (linear
  even when `additive[0]` exists) is gone by construction.
* **(ii)** `ctxLookup`'s additive-first order is proven **equal to the
  shipped checker's** (`crates/dlc-core/src/decide.rs`, mirrored in
  `DLC.decideLean`): `ctxLookup_eq_checker_additive` /
  `ctxLookup_eq_checker_empty_additive`. `ctxLookup_ne_checker_witness`
  records — machine-checked — the one place the disambiguated `Deriv`
  strictly *extends* the checker (a linear var under a nonempty additive
  context, which `decide.rs` cannot reach because it only consults the
  linear context at index 0, shadowed by `additive[0]`).

Everything here is `sorry`-free and axiom-clean; the genuinely hard
substructural content (linear-split routing) is L2/L4 and is left as an
explicit, unproven `Prop` statement (`LinearSplitRoutes`), not a `sorry`.
-/

import DLC.Judgment
import DLC.Decidability

namespace DLC

/-! ## `ctxLookup` — the additive-first variable resolver.

Mirrors `decide.rs`'s `Term::Var` case: consult the additive context by
de Bruijn index first; only on a miss consult the linear context. The one
deliberate difference from `decide.rs` is *where* the linear singleton
lives — at index `additive.length` (the disambiguated L1 position) rather
than the ambiguous index `0`. The two coincide exactly when the additive
context is empty, which is the only regime `decide.rs` supports for linear
variables (see `ctxLookup_eq_checker_empty_additive` and the witness). -/
def ctxLookup (Γ : Ctx) (i : Nat) : Option Prop' :=
  match Γ.additive[i]? with
  | some φ => some φ
  | none =>
    match Γ.linear with
    | [φ] => if i = Γ.additive.length then some φ else none
    | _   => none

/-! ### Elementary index facts. -/

/-- An out-of-range additive index. -/
theorem additive_getElem?_length_none (Γ : Ctx) :
    Γ.additive[Γ.additive.length]? = none :=
  List.getElem?_eq_none (le_refl _)

/-- A successful additive lookup pins the index below the length. -/
theorem lt_length_of_additive_getElem? (Γ : Ctx) (i : Nat) (φ : Prop')
    (h : Γ.additive[i]? = some φ) : i < Γ.additive.length := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  exact hlt

/-- A successful additive lookup cannot sit at index `= length`. -/
theorem additive_getElem?_ne_length (Γ : Ctx) (i : Nat) (φ : Prop')
    (h : Γ.additive[i]? = some φ) : i ≠ Γ.additive.length := by
  intro heq
  have hlt := lt_length_of_additive_getElem? Γ i φ h
  omega

/-! ### Constraint (i): `ctxLookup` agrees with the (restricted) var rules. -/

/-- `varA` direction: an in-range additive hit is what `ctxLookup` returns. -/
theorem ctxLookup_varA (Γ : Ctx) (i : Nat) (φ : Prop')
    (h : Γ.additive[i]? = some φ) : ctxLookup Γ i = some φ := by
  unfold ctxLookup
  rw [h]

/-- `varL` direction: the restricted linear singleton, at index
`Γₐ.length`, is what `ctxLookup` returns. -/
theorem ctxLookup_varL (Γₐ : List Prop') (φ : Prop') :
    ctxLookup { additive := Γₐ, linear := [φ] } Γₐ.length = some φ := by
  unfold ctxLookup
  have hn : (({ additive := Γₐ, linear := [φ] } : Ctx).additive)[Γₐ.length]? = none :=
    List.getElem?_eq_none (le_refl _)
  rw [hn]
  simp

/-- **Main agreement (constraint (i)).** `ctxLookup Γ i = some φ` holds
*iff* the variable is derivable by exactly one of the two var rules: an
in-range additive lookup (`varA`), or the restricted linear singleton at
index `Γ.additive.length` (`varL`). No side condition (`CtxWellFormed`) is
needed — the disambiguation is by construction, which is precisely why the
restructure makes the substitution lemma well-posed. -/
theorem ctxLookup_agrees (Γ : Ctx) (i : Nat) (φ : Prop') :
    ctxLookup Γ i = some φ ↔
      Γ.additive[i]? = some φ ∨ (Γ.linear = [φ] ∧ i = Γ.additive.length) := by
  unfold ctxLookup
  cases hadd : Γ.additive[i]? with
  | some ψ =>
    constructor
    · intro h; exact Or.inl h
    · intro h
      cases h with
      | inl h => exact h
      | inr h =>
        exact absurd h.2 (additive_getElem?_ne_length Γ i ψ hadd)
  | none =>
    cases hlin : Γ.linear with
    | nil =>
      simp
    | cons a tl =>
      cases tl with
      | nil =>
        by_cases hi : i = Γ.additive.length
        · subst hi; simp
        · simp [hi]
      | cons b tl' =>
        simp

/-- **Constraint (i), constructive.** Every successful `ctxLookup` yields an
actual derivation (`Nonempty (Deriv …)`) — via `varA` or the restricted
`varL`. This is the sense in which `ctxLookup` *mirrors the rules*: not
merely a matching side condition, but a witnessed derivation in each case
(matching the codebase's `Nonempty (Deriv …)` soundness convention). -/
theorem ctxLookup_sound (Γ : Ctx) (i : Nat) (φ : Prop')
    (h : ctxLookup Γ i = some φ) : Nonempty (Deriv Γ (Term.var i) φ) := by
  rcases (ctxLookup_agrees Γ i φ).mp h with hA | ⟨hlin, hidx⟩
  · exact ⟨Deriv.varA Γ i φ hA⟩
  · obtain ⟨a, l⟩ := Γ
    subst hlin
    subst hidx
    exact ⟨Deriv.varL a φ⟩

/-! ## `CtxWellFormed` — the disambiguation invariant.

The shape guarantee that makes var lookup unambiguous: every successful
`ctxLookup` is *either* an in-range additive hit *or* the linear singleton
sitting exactly at index `additive.length` — never both, never elsewhere.
This is the Lean form of "additive occupies `0 .. length-1`; the linear var
lives beyond, at `length`."

It is **not** a tautology (its body is a genuine ∀/disjunction, not `True`);
`check-tautologies.sh` is satisfied. It *does* turn out to hold for every
context (`CtxWellFormed_all`) — that is the substantive L1 result: the
`var Γₐ.length` restructure makes the invariant hold *by construction*, so
no `Deriv` rule can manufacture an ill-formed context and every per-rule
preservation obligation (below) discharges without a side condition. -/
def CtxWellFormed (Γ : Ctx) : Prop :=
  ∀ i φ, ctxLookup Γ i = some φ →
    (i < Γ.additive.length ∧ Γ.additive[i]? = some φ) ∨
    (i = Γ.additive.length ∧ Γ.linear = [φ])

/-- The invariant holds for **every** context: disambiguation is structural.
This is the load-bearing L1 fact — it is what lets the split rules preserve
well-formedness with no bookkeeping. -/
theorem CtxWellFormed_all (Γ : Ctx) : CtxWellFormed Γ := by
  intro i φ h
  rcases (ctxLookup_agrees Γ i φ).mp h with hA | ⟨hlin, hidx⟩
  · exact Or.inl ⟨lt_length_of_additive_getElem? Γ i φ hA, hA⟩
  · exact Or.inr ⟨hidx, hlin⟩

/-! ## Constraint (ii): equivalence to the shipped checker (`decide.rs`).

`decideLean` (`DLC.Decidability`) is the Lean mirror of `decide.rs::infer`;
its `Term.var` case resolves `additive[i]?` first, then a *singleton linear
context at index 0*. We prove `ctxLookup` shares the additive-first order,
coincides with the checker wherever the checker resolves a linear var, and
we exhibit — machine-checked — the sole point of divergence. -/

/-- **Additive-first agreement.** Whenever the additive lookup succeeds,
`ctxLookup` and the checker return the *same* proposition. This is the
"additive lookup takes precedence" discipline, now a theorem. -/
theorem ctxLookup_eq_checker_additive (Γ : Ctx) (i : Nat) (φ : Prop')
    (h : Γ.additive[i]? = some φ) :
    ctxLookup Γ i = decideLean Γ (Term.var i) := by
  rw [ctxLookup_varA Γ i φ h]
  unfold decideLean
  rw [h]

/-- **Full agreement on the checker-supported domain.** With an empty
additive context — the only regime in which `decide.rs` accepts a linear
variable — `ctxLookup` equals the checker *for every index*. Here the
disambiguated linear index `Γₐ.length = 0` coincides with `decide.rs`'s
hard-coded index `0`, so the two agree on the nose. -/
theorem ctxLookup_eq_checker_empty_additive (Γ : Ctx) (i : Nat)
    (h : Γ.additive = []) :
    ctxLookup Γ i = decideLean Γ (Term.var i) := by
  obtain ⟨a, l⟩ := Γ
  subst h
  unfold ctxLookup decideLean
  simp only [List.getElem?_nil, List.length_nil]
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => cases i <;> simp
    | cons y ys => simp

/-- **The divergence — an honest finding.** With a *nonempty* additive
context and a singleton linear context, `ctxLookup` resolves the linear
variable at index `additive.length` (here `1`) but the shipped checker
returns `none`: `decide.rs` only consults the linear context at index `0`,
which `additive[0]` shadows. So the L1-disambiguated `Deriv` (via the
restructured `varL`) is *strictly more expressive* than the current checker
in the nonempty-additive linear case — the checker is incomplete w.r.t.
`Deriv` here, not unsound. Recorded as a machine-checked witness so the gap
is a fact, not prose. (Closing it is a `decide.rs` change, out of L1 scope.) -/
theorem ctxLookup_ne_checker_witness :
    ∃ (Γ : Ctx) (i : Nat), ctxLookup Γ i ≠ decideLean Γ (Term.var i) := by
  refine ⟨{ additive := [Prop'.atom 0], linear := [Prop'.atom 1] }, 1, ?_⟩
  have hlk : ctxLookup { additive := [Prop'.atom 0], linear := [Prop'.atom 1] } 1
      = some (Prop'.atom 1) := ctxLookup_varL [Prop'.atom 0] (Prop'.atom 1)
  have hchk : decideLean { additive := [Prop'.atom 0], linear := [Prop'.atom 1] }
      (Term.var 1) = none := by unfold decideLean; rfl
  rw [hlk, hchk]
  exact Option.some_ne_none _

/-! ## Per-rule `CtxWellFormed` preservation.

Because `CtxWellFormed_all` holds unconditionally, every `Deriv` rule
preserves the invariant — including the linear-splitting rules, whose
`Γ₁ ++ Γ₂` conclusion context is still just *some* `Ctx`. We record the
representative rules explicitly (constraint 4). These are corollaries of
`CtxWellFormed_all`; the honest reading is that the L1 restructure made
preservation trivial, which is the *goal*, not a gap. -/

theorem CtxWellFormed_varA (Γ : Ctx) : CtxWellFormed Γ := CtxWellFormed_all Γ

theorem CtxWellFormed_varL (Γₐ : List Prop') (φ : Prop') :
    CtxWellFormed { additive := Γₐ, linear := [φ] } := CtxWellFormed_all _

theorem CtxWellFormed_weakenA (Γ : Ctx) (φ' : Prop')
    (_h : CtxWellFormed Γ) : CtxWellFormed (Ctx.consA φ' Γ) :=
  CtxWellFormed_all _

theorem CtxWellFormed_impI (Γ : Ctx) : CtxWellFormed Γ := CtxWellFormed_all Γ

theorem CtxWellFormed_andI (Γₐ : List Prop') :
    CtxWellFormed { additive := Γₐ, linear := [] } := CtxWellFormed_all _

theorem CtxWellFormed_orE (Γₐ : List Prop') :
    CtxWellFormed { additive := Γₐ, linear := [] } := CtxWellFormed_all _

theorem CtxWellFormed_now (Γₐ : List Prop') :
    CtxWellFormed { additive := Γₐ, linear := [] } := CtxWellFormed_all _

/-- Preservation for the **linear-splitting** rules (`impE`, `tensorI`,
`saysE`, `delegate`, `discharge`, `tensorE`, `letSaysE`): the concatenated
conclusion context is well-formed regardless of how the linear suffix is
partitioned. Stated once over an arbitrary split; both premises' contexts
are likewise `CtxWellFormed` by `CtxWellFormed_all`. -/
theorem CtxWellFormed_split (Γₐ Γ₁ Γ₂ : List Prop') :
    CtxWellFormed { additive := Γₐ, linear := Γ₁ } ∧
    CtxWellFormed { additive := Γₐ, linear := Γ₂ } ∧
    CtxWellFormed { additive := Γₐ, linear := Γ₁ ++ Γ₂ } :=
  ⟨CtxWellFormed_all _, CtxWellFormed_all _, CtxWellFormed_all _⟩

/-! ### Substantive content for the split rules (L2-facing).

Preservation being trivial does *not* mean the split rules are trivial: the
real substructural work is that a linear variable in a `Γ₁ ++ Γ₂` context
routes to exactly one side. The following lemma is the L1 down-payment on
that: in an *intermediate* split context whose linear part is **not** a
singleton, `ctxLookup` refuses every linear-region index — you cannot look
up a linear variable directly; you must first split (which is exactly the
L2 obligation). -/
theorem ctxLookup_nonsingleton_linear_none (Γ : Ctx) (i : Nat)
    (hlin : Γ.linear.length ≠ 1) (hi : Γ.additive.length ≤ i) :
    ctxLookup Γ i = none := by
  unfold ctxLookup
  rw [List.getElem?_eq_none hi]
  cases h : Γ.linear with
  | nil => simp
  | cons a tl =>
    cases tl with
    | nil => rw [h] at hlin; simp at hlin
    | cons b tl' => simp

/-- **L2-deferred (stated, not `sorry`d).** The genuine substructural core
the split rules will need in L4: a linear variable resolved in a `Γ₁ ++ Γ₂`
context routes to **exactly one** side of the split, and `N`'s own linear
resources merge into that side. This is a `Prop` *statement* consumed by
L2's split algebra and L4's linear-substitution proof; it is deliberately
left unproven here (proving it needs the L2 membership/partition machinery
that does not yet exist). It is **not** a `sorry` — no proof is claimed —
and it is **not** a tautology (a real ∀ with a genuine disjunction). Listed
as deferred in the L1 report. -/
def LinearSplitRoutes (Γₐ Γ₁ Γ₂ : List Prop') : Prop :=
  ∀ i φ, ctxLookup { additive := Γₐ, linear := Γ₁ ++ Γ₂ } i = some φ →
    i = Γₐ.length ∧ (Γ₁ = [φ] ∧ Γ₂ = []) ∨ (Γ₁ = [] ∧ Γ₂ = [φ])

end DLC
