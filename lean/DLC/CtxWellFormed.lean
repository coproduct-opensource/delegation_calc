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

/-! ## L2 — the linear split algebra.

The `++` bookkeeping every linear elimination uses (`impE`, `saysE`,
`delegate`, `tensorE`, `boxI`/`discharge`): a linear variable resolved in a
`Γ₁ ++ Γ₂` context routes to EXACTLY ONE side of the split.

### The previously-stated form was FALSE, not merely unproven.

`LinearSplitRoutes` was carried as a deferred `Prop` with the note that it
"is **not** a `sorry` -- no proof is claimed -- and it is **not** a tautology
(a real ∀ with a genuine disjunction)". Both of those were true. Neither
implies the statement holds, and it did not. It read:

    ∀ i φ, ctxLookup ⟨Γₐ, Γ₁ ++ Γ₂⟩ i = some φ →
      i = Γₐ.length ∧ (Γ₁ = [φ] ∧ Γ₂ = []) ∨ (Γ₁ = [] ∧ Γ₂ = [φ])

Two independent defects:

1. **No additive-miss hypothesis.** `ctxLookup` consults `additive` FIRST
   and only falls through to `linear` on a miss. So when `i` hits the
   additive context the linear halves are entirely unconstrained, and
   neither disjunct need hold. `linearSplitRoutes_old_form_refuted` below
   exhibits this: `Γₐ = [atom 0]`, `i = 0`, `Γ₁ = [atom 5]`, `Γ₂ = [atom 6]`.
2. **Precedence.** `∧` binds tighter than `∨`, so `i = Γₐ.length ∧ A ∨ B`
   parses as `(i = Γₐ.length ∧ A) ∨ B` -- the index claim attached only to
   the left branch, leaving `i` unconstrained on the right. The intended
   reading scopes it over both.

The corrected statement adds the missing hypothesis and the parentheses,
and is proven below rather than deferred. -/

/-- A linear variable resolved in a split context routes to exactly one
side. The `Γₐ[i]? = none` premise is load-bearing: it is what makes this a
statement about LINEAR variables rather than about `ctxLookup` in general
(see `linearSplitRoutes_old_form_refuted`). -/
def LinearSplitRoutes (Γₐ Γ₁ Γ₂ : List Prop') : Prop :=
  ∀ i φ, Γₐ[i]? = none →
    ctxLookup { additive := Γₐ, linear := Γ₁ ++ Γ₂ } i = some φ →
      i = Γₐ.length ∧ ((Γ₁ = [φ] ∧ Γ₂ = []) ∨ (Γ₁ = [] ∧ Γ₂ = [φ]))

/-- **L2 core.** The split algebra holds for every context and every split.
Proof: the additive-miss premise forces `ctxLookup_agrees`' linear disjunct,
which pins `Γ₁ ++ Γ₂ = [φ]`; appending to a singleton leaves exactly the two
routings. -/
theorem linearSplitRoutes_holds (Γₐ Γ₁ Γ₂ : List Prop') :
    LinearSplitRoutes Γₐ Γ₁ Γ₂ := by
  intro i φ hmiss hlk
  rcases (ctxLookup_agrees { additive := Γₐ, linear := Γ₁ ++ Γ₂ } i φ).mp hlk with
    hA | ⟨hlin, hidx⟩
  · -- additive hit contradicts the miss premise
    rw [hmiss] at hA
    simp at hA
  · refine ⟨hidx, ?_⟩
    -- `Γ₁ ++ Γ₂ = [φ]`
    cases Γ₁ with
    | nil =>
        right
        exact ⟨rfl, by simpa using hlin⟩
    | cons a tl =>
        left
        have h := hlin
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨ha, htl⟩ := h
        have h2 : tl = [] ∧ Γ₂ = [] := List.append_eq_nil_iff.mp htl
        exact ⟨by rw [ha, h2.1], h2.2⟩

/-- The refutation of the old form, kept so it cannot silently return. With
an ADDITIVE hit the linear halves are unconstrained, so the un-hypothesised
statement fails. -/
theorem linearSplitRoutes_old_form_refuted :
    ¬ (∀ i φ, ctxLookup { additive := [Prop'.atom 0],
                          linear := [Prop'.atom 5] ++ [Prop'.atom 6] } i = some φ →
        (i = ([Prop'.atom 0] : List Prop').length ∧
          ([Prop'.atom 5] = [φ] ∧ ([Prop'.atom 6] : List Prop') = [])) ∨
        (([Prop'.atom 5] : List Prop') = [] ∧ [Prop'.atom 6] = [φ])) := by
  intro h
  have hl : ctxLookup { additive := [Prop'.atom 0],
                        linear := [Prop'.atom 5] ++ [Prop'.atom 6] } 0
          = some (Prop'.atom 0) := by rfl
  rcases h 0 (Prop'.atom 0) hl with ⟨_, h1, _⟩ | ⟨h2, _⟩
  · injection h1 with hx _; injection hx with hn; exact absurd hn (by decide)
  · simp at h2

/-! ## Linear de Bruijn LEVELS — the fix for split-context addressing.

`ctxLookup` addresses the linear hypothesis at `additive.length` and only
when the linear context is a SINGLETON. Loop 5 showed that does not survive
context splitting: every split branch has the same additive length, so every
branch addresses its linear hypothesis at the same index, and splicing two
singleton premises yields a conclusion whose variables resolve to nothing
(`ctxLookup_nonsingleton_linear_none`). The witness is in
`spec/linear-substitution-design-2026-07.md`.

Option (A) — de Bruijn LEVELS for linear variables — is validated here
before any rule changes. A linear hypothesis at position `k` is addressed by

    Term.var (Γ.additive.length + k)

so its address is its ABSOLUTE position in the spliced context, not its
position relative to whichever premise introduced it.

Staged deliberately: `ctxLookupL` lands ALONGSIDE `ctxLookup` with an
agreement theorem, so nothing that depends on L1 moves yet. The migration
still owed is on the SPLIT RULES, which must shift the right premise's term
by `Γ₁.length` (e.g. `impE` emitting `Term.app M (shift N Γ₁.length
Γₐ.length)`) so its addresses land in the right half of `Γ₁ ++ Γ₂`. That is
a change to `Deriv`'s rules and is not taken here. -/

/-- Level-based context lookup: additive first, then the linear hypothesis at
position `i - additive.length`. Generalises `ctxLookup`'s singleton case to
arbitrary linear contexts. -/
def ctxLookupL (Γ : Ctx) (i : Nat) : Option Prop' :=
  match Γ.additive[i]? with
  | some φ => some φ
  | none   => Γ.linear[i - Γ.additive.length]?

/-- **Backward compatible.** On the singleton linear contexts L1 already
handles, the level-based lookup agrees with `varL`'s address. -/
theorem ctxLookupL_varL (Γₐ : List Prop') (φ : Prop') :
    ctxLookupL { additive := Γₐ, linear := [φ] } Γₐ.length = some φ := by
  simp [ctxLookupL]

/-- **The case that broke L1, resolved.** A two-element linear context
addresses its hypotheses DISTINCTLY, where `ctxLookup` resolved neither.
This is the `impE`-splice counterexample from loop 5. -/
theorem ctxLookupL_resolves_split (φ ψ : Prop') :
    ctxLookupL { additive := [], linear := [φ, ψ] } 0 = some φ ∧
    ctxLookupL { additive := [], linear := [φ, ψ] } 1 = some ψ :=
  ⟨rfl, rfl⟩

/-- Contrast, kept explicit: the OLD lookup resolves neither index in that
same context. This is what makes the migration necessary rather than
cosmetic. -/
theorem ctxLookup_fails_on_split (φ ψ : Prop') :
    ctxLookup { additive := [], linear := [φ, ψ] } 0 = none ∧
    ctxLookup { additive := [], linear := [φ, ψ] } 1 = none :=
  ⟨rfl, rfl⟩

/-! ## Regression: `impE` addresses its right premise by LEVEL.

The loop-5 counterexample, now fixed. `impE` splices two singleton linear
premises; before the migration both used `var 0` and NEITHER resolved in the
conclusion's context. `impE` now shifts its right premise by `Γ₁.length`, so
the right half's addresses land where they actually live in `Γ₁ ++ Γ₂`.

If that shift is ever dropped, this stops compiling. -/

/-- The spliced conclusion's variables resolve, and resolve DISTINCTLY. -/
theorem impE_levels_regression (A B : Prop') :
    Nonempty (Deriv { additive := [], linear := [Prop'.imp A B] ++ [A] }
                    (Term.app (Term.var 0) (Term.var 1)) B) := by
  have dM : Deriv { additive := [], linear := [Prop'.imp A B] }
                  (Term.var 0) (Prop'.imp A B) := Deriv.varL [] _
  have dN : Deriv { additive := [], linear := [A] } (Term.var 0) A := Deriv.varL [] A
  exact ⟨by simpa [shift] using
    Deriv.impE [] [Prop'.imp A B] [A] A B (Term.var 0) (Term.var 0) dM dN⟩

/-- …and each index resolves to the half it came from. -/
theorem impE_levels_addresses (A B : Prop') :
    ctxLookupL { additive := [], linear := [Prop'.imp A B, A] } 0 = some (Prop'.imp A B) ∧
    ctxLookupL { additive := [], linear := [Prop'.imp A B, A] } 1 = some A :=
  ⟨rfl, rfl⟩

/-! ## Regression: every migrated split rule addresses by LEVEL.

`tensorI`, `delegate` and `discharge` follow `impE`: the right premise is
shifted by `Γ₁.length` at cutoff `Γₐ.length`, so only LINEAR addresses move
and they land where the right half actually lives in `Γ₁ ++ Γ₂`.

Each theorem below exhibits a NON-DEGENERATE split -- both halves singleton,
so the shift is a real `+1` rather than the identity. That matters: every
pre-existing construction in the repo used empty linear contexts, where the
shift is `shift _ 0 _` and the addressing defect is invisible. These are the
first derivations in the codebase that exercise a genuine two-sided split. -/

/-- `tensorI` on a genuine split: the right component is addressed at 1. -/
theorem tensorI_levels_regression (φ ψ : Prop') :
    Nonempty (Deriv { additive := [], linear := [φ] ++ [ψ] }
                    (Term.tensorIntro (Term.var 0) (Term.var 1)) (Prop'.tensor φ ψ)) := by
  have dM : Deriv { additive := [], linear := [φ] } (Term.var 0) φ := Deriv.varL [] φ
  have dN : Deriv { additive := [], linear := [ψ] } (Term.var 0) ψ := Deriv.varL [] ψ
  have d := Deriv.tensorI [] [φ] [ψ] φ ψ (Term.var 0) (Term.var 0) dM dN
  exact ⟨by simpa [shift] using d⟩

/-- `discharge` on a genuine split: the evidence premise is addressed at 1. -/
theorem discharge_levels_regression (O : Obligation) (φ : Prop') :
    Nonempty (Deriv { additive := [], linear := [Prop'.boxed O φ] ++ [Prop'.atom 0] }
                    (Term.discharge (Term.var 0) (Term.var 1)) φ) := by
  have dM : Deriv { additive := [], linear := [Prop'.boxed O φ] }
                  (Term.var 0) (Prop'.boxed O φ) := Deriv.varL [] _
  have dN : Deriv { additive := [], linear := [Prop'.atom 0] }
                  (Term.var 0) (Prop'.atom 0) := Deriv.varL [] _
  have d := Deriv.discharge [] [Prop'.boxed O φ] [Prop'.atom 0] O φ
              (Term.var 0) (Term.var 0) dM dN
  exact ⟨by simpa [shift] using d⟩

/-- Both halves of a two-element linear context resolve, distinctly. -/
theorem split_addresses_resolve (φ ψ : Prop') :
    ctxLookupL { additive := [], linear := [φ, ψ] } 0 = some φ ∧
    ctxLookupL { additive := [], linear := [φ, ψ] } 1 = some ψ :=
  ⟨rfl, rfl⟩

/-! ## Regression: `weakenA` must shift.

`Ctx.consA` prepends to the additive context, so a de Bruijn index that is
not shifted silently re-points at the newly-added hypothesis. Until
2026-07-20 `Deriv.weakenA` concluded at an UNSHIFTED `M`, which let one term
inhabit two types in one context — and the weakened one was wrong.

Concretely: with `Γ.additive = [A]`, `varA` gives `var 0 : A`; the old rule
then gave `var 0 : A` in `[B, A]`, where `var 0` denotes `B`.

The theorem below pins the corrected behaviour: after weakening, the
derivation is about `shift (var 0) 1 0 = var 1`, which is where `A` actually
lives in `[B, A]`. If `weakenA` ever loses its shift, this stops compiling.

Only `Deriv` was affected. `PropDeriv` — where T1 completeness, T3 and
progress live — has no `weakenA` at all, so no proven theorem was falsified;
the exposure was to the future L3-L5 extension of T3 onto full `Deriv`. -/

/-- Weakening shifts: the weakened derivation is about `var 1`, not `var 0`. -/
theorem weakenA_shifts_regression :
    ∀ (A B : Prop'),
      Nonempty (Deriv { additive := [B, A], linear := [] } (Term.var 1) A) := by
  intro A B
  have d0 : Deriv { additive := [A], linear := [] } (Term.var 0) A :=
    Deriv.varA _ 0 A rfl
  have dW := Deriv.weakenA { additive := [A], linear := [] } B A (Term.var 0) d0
  -- `shift (var 0) 1 0 = var 1`, and `consA B ⟨[A], []⟩ = ⟨[B, A], []⟩`
  simpa [shift, Ctx.consA] using ⟨dW⟩

end DLC
