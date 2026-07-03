# The linear lever — design for extending the metatheory to full `Deriv`

**Controller tick #1 (autonomous, 2026-07-03).** The persona controller's Observe
step ranked `substitution_lemma` (full `Deriv`, linear cases) as the highest-leverage
open item: it is the shared root that unblocks **subject_reduction-full → T3-full,
T1-full, progress-full** — four theorems on one lever, exactly the abstraction the
rubric prizes. This doc is the design that must precede the proof, and it surfaces
the real blocker (below) the way `t3-two-run-design`'s FINDING did for T3.

Nothing here is proven; statuses live in `lean/theorem-status.json`.

## THE BLOCKER (2026-07-03): additive and linear variables share one de Bruijn space

`Deriv`'s two variable rules (`lean/DLC/Judgment.lean`):

```
varA : Γ.additive[i]? = some φ  →  Deriv Γ (Term.var i) φ
varL :                              Deriv {additive := Γₐ, linear := [φ]} (Term.var 0) φ
```

`Term.var 0` is therefore **ambiguous** — it can be `additive[0]` (via `varA`) *or*
the sole linear hypothesis (via `varL`). Additive (re-usable) and linear
(single-use) hypotheses are indexed into the *same* `Term.var` space, with
overlapping lookup. Consequences:

* **This is why the propositional fragment closed and full `Deriv` did not.**
  `PropDeriv` is **additive-only** (`Γₐ[i]?`, no linear context) — it never meets the
  overlap, so rungs 1–3c went through. Full `Deriv` mixes both, and the substitution
  lemma cannot even be *stated* cleanly: "substitute `N` for the variable at index
  `k`" is ill-posed when index `k` might be additive (duplicable — `N` must be usable
  in every premise) or linear (single-use — `N`'s own linear resources must route to
  exactly the one consuming premise, splitting the `Γ₁ ++ Γ₂`).
* It is the same wall behind T1-full, T4-multiset, and subject-reduction-full. Knock
  it down once; four theorems advance.

## The resolution: formalize the invariant the checker already enforces

The Rust `infer` / `decideLean` **already disambiguates**
(`crates/dlc-core/src/decide.rs`): a `var i` resolves to `additive[i]` when that
exists, and only *else* to the linear context. So there is an operative discipline —
**additive lookup takes precedence; linear variables live at indices beyond the
additive context** — that is merely not yet a Lean invariant. Making it one
(`CtxWellFormed`: linear hypotheses occupy `var` indices ≥ `additive.length`, never
colliding with an additive index) makes the substitution lemma well-posed **without a
syntax or wire-format change** — the cheaper of the two paths:

| path | cost | verdict |
|---|---|---|
| Separate syntax (`Term.lvar` / tagged linear index) | `Term` change → wire format → full spec→Tamarin→wire→code ceremony | rejected for now — too heavy, and the checker doesn't need it |
| **`CtxWellFormed` invariant (additive-first, linear-beyond)** | Lean-only; mirrors the shipped checker | **chosen** |

## Rung decomposition (the campaign, in dependency order)

- **L1 — disambiguation invariant.** `CtxWellFormed Γ`: `Γ.linear` occupies `var`
  indices `≥ Γ.additive.length`. Prove every `Deriv` rule preserves it (the split
  `Γ₁ ++ Γ₂` distributes the linear suffix). *Bounded; this is the next dispatch.*
  **Two binding constraints (from the D-review of this doc, PR #101):**
  (i) `varL` as written permits *nonempty* `Γₐ` — `var 0 → linear` even when
  `additive[0]` exists, which the checker does NOT honor. L1 must therefore
  actually **restrict** `varL` under the invariant (linear singleton only when it
  cannot collide with an additive index), not merely add an orthogonal predicate.
  (ii) `CtxWellFormed`'s additive-first lookup order must be **proven equivalent** to
  `decide.rs`'s (`additive.get` then linear-on-miss) — machine-checked, not asserted
  in prose — so "mirrors the shipped checker" is a theorem.
- **L2 — linear context split algebra.** The `++` bookkeeping every linear
  elimination uses (`impE`, `saysE`, `delegate`, `tensorE`, `boxI`/discharge):
  membership/partition/associativity over `Γ₁ ++ Γ₂`, and the "resources are
  consumed exactly once" accounting. Pure `List Prop'`; bounded.
- **L3 — additive substitution preservation over full `Deriv`.** The *easier* half:
  an additive hypothesis is shared across all premises (same `Γₐ` everywhere), so its
  substitution recurses uniformly, threading the linear contexts along unchanged. The
  28-constructor analog of the PropDeriv result already proven; reuses that induction
  shape. `N` typed additive-only (`linear := []`) so it may be duplicated.
- **L4 — linear substitution preservation (the hard case).** Substituting for a
  *linear* hypothesis: the variable lands in exactly one side of each `Γ₁ ++ Γ₂`
  split; `N`'s own linear resources merge into that side. Needs L1+L2. This is the
  genuine substructural core — the multi-week piece.
- **L5 — subject reduction over full `Deriv`**, then **T3-full / T1-full /
  progress-full** follow by re-running the existing fragment proofs over the extended
  substitution/reduction machinery, with `declassify` still excluded by design.

## Non-goals / honest scope

- No `Term` / wire-format change (path 1 rejected). If L4 proves impossible under the
  shared-index invariant, revisit path 1 — but only then, and with the full ceremony.
- `declassify` stays excluded (NI modulo declassification, as in T3).
- Complexity bound (`O(|M|·log|Γ|)`) is a *separate* open item, not on this lever.

**Next tick:** dispatch L1 (`CtxWellFormed` + per-rule preservation + the two
binding constraints above) — bounded, hand-verifiable, and the gate that makes L4's
statement well-posed.
