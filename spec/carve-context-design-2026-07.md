# Contexts as resource vectors — the L3/L4 representation migration

**Status:** design accepted 2026-07-20. Supersedes rungs L1 and L2 of
`linear-substitution-design-2026-07.md`.

## The problem this replaces

That document opens with:

> **THE BLOCKER (2026-07-03): additive and linear variables share one de
> Bruijn space.**

The repo's chosen resolution was to keep the split `{additive, linear}`
context and formalize a disambiguation invariant (L1) pinning the linear
variable to index `additive.length`, plus a split algebra (L2). Both landed
and both are proven.

They do not survive contact with the metatheory. L3a — additive
weakening-in-the-middle over full `Deriv` — proves **26 of 28** cases and
then fails on `tensorE` for a reason that is not proof engineering. Both
halves are pinned as compiling theorems in `DLC/CtxWellFormed.lean`:

* `varL_linear_binders_are_indistinguishable` — `Deriv.varL` concludes at
  `Term.var Γₐ.length`, an index depending only on the **additive** context
  length. Every linear hypothesis in a context is therefore denoted by the
  **same** term. Linear binders consume **zero** de Bruijn slots.
* `shift_letTensor_reserves_two_slots` — yet `shift` skips **two** for
  `letTensor`'s body.

`tensorE` binds its two hypotheses linearly, so L3a's goal demands the body
shifted at `Γl.length + 2` while the induction hypothesis supplies
`Γl.length`. No shift-commutation lemma bridges them, and none should:
additive variables at levels in `[Γl.length, Γl.length + 2)` would then
wrongly fail to move. The `+ 2` is *correct* for `letTensorA`, whose binders
really are additive. `Term.letTensor` is overloaded across two rules with
incompatible shift semantics — the same species as the `saysE`/`letSaysE`
overload that `Term.saysBind` resolved in #131.

Patching `tensorE` alone would be the third fix of that shape. Two was
already a pattern.

## The replacement

Follow CARVe — *Contexts as Resource Vectors* (Zackon, Kavanagh,
Momigliano, Pientka; RocqPL 2026; full version *Split decisions: Explicit
contexts for substructural languages*, CPP '25).

A context becomes **one vector of tagged hypotheses that is never
restructured**:

```
Ctx := List (Prop' × Mult)
Mult := zero | one | many          -- consumed | linear | unrestricted
```

A context "split" becomes an **elementwise join** at the *same length*:
positions and types are identical in both operands and the result; only
tags differ.

```
CJoin Γ₁ Γ₂ Γ    with   zero + m = m,   many + many = many
```

Linearity stops being a syntactic property of context shape and becomes a
semantic one carried by annotations. Quoting the paper:

> context splits require no index shifting or renaming to preserve
> well-scopedness, since CARVe contexts remain structurally intact across
> splits: the datatype of terms is identical to that used for the systems'
> ordinary intuitionistic counterparts.

### What follows for DLC

| | |
|---|---|
| `varA` / `varL` | collapse into **one** rule looking up the entry at its position. No disambiguation invariant is needed, because there is nothing to disambiguate. |
| Split rules (`impE`, `tensorI`, `delegate`, `discharge`, `saysE`, `letSaysE`, `tensorE`) | `Γ₁ ++ Γ₂` becomes `CJoin Γ₁ Γ₂ Γ`. Lengths do not change, so **no rule carries a `shift` in its conclusion**. |
| `tensorE` | its binders extend the context by two, so they occupy two real slots and `shift`'s `+ 2` becomes correct **by construction**. |
| `shift_shift_comm` (#129) | no longer needed by L3a. |
| L4 | the paper reports substitution-preservation-across-splits as a *near-immediate* lemma. This is the whole reason to do the migration. |

## Validation

This is not adopted on the strength of the paper. `lean/CarveProto.lean` is
a self-contained miniature calculus in this representation — `var`, `lam`,
`app`, `tenI`, `letT` — which **proves** weakening-in-the-middle
(`d_shift`), *including the `letT` case that resists in the real `Deriv`*.

Checked three ways:

1. compiles with zero errors and zero warnings;
2. `#print axioms d_shift` = `[propext, Quot.sound]` — no `sorryAx`;
3. **perturbed**: changing `shift`'s `letT` clause from `c + 2` to `c + 1`
   breaks *only* the `letT` case, at the exact step reconciling the cutoff.

The third check is the load-bearing one. A green build establishes nothing
until it is shown to fail for the right reason at the right place.

Two things are **absent** from that proof, and their absence is the result:
no shift-commutation lemma anywhere (no conclusion carries a shift), and no
re-indexing after a split (`cjoin_split` partitions tags and moves no
index). Those are precisely the costs the current representation pays on
every rule.

**Known gap.** The prototype does not model the linear-*usage* side
condition on the variable rule — that every *other* linear position is
consumed. That is a soundness condition, orthogonal to the indexing
question under test. It is expected to go through, since inserted blocks
are `zero`-tagged, but it is **not proven**, and the migration must close
it rather than inherit the assumption.

## Blast radius (measured, not estimated)

Lean files referencing `Ctx.additive` / `Ctx.linear`:

| file | refs |
|---|---|
| `DLC/Decidability.lean` | 63 |
| `DLC/CtxWellFormed.lean` | 62 |
| `DLC/Judgment.lean` | 40 |
| `DLC/ProtocolCorrespondence.lean` | 2 |
| `DLC/NonInterference.lean` | 1 |

`Subst`, `Reduce`, `ReduceMeta`, `Progress`, `ObligationSoundness` and the
`NonInterference*` proofs are untouched: they live on `PropDeriv`, which
has no linear structure. **No proven headline theorem is at risk** — this
is the cheapest this change will ever be, and it gets more expensive with
every rung built on the current representation.

Rust: `dlc-core/{syntax,judgment,decide,graded,obligation}.rs`,
`dlc-verifier/check.rs`, `dlc-grade-quantale/lib.rs`.

Two constraints that do **not** bite:

* **`Ctx` is not on the wire** (zero references in `dlc-protocol/src/wire.rs`),
  so the §4.4 correspondence theorem is untouched and no Tamarin model
  change is required — `CLAUDE.md`'s ban on unmodelled wire changes does
  not apply.
* The verifier is **173 LOC against a 2000 budget**.

`dlc-grade-quantale` already defines a `Quantale` trait with
`unit()`/`tensor()` — the right *shape* for a resource algebra. But `Spend`
and `Risk` are DP-budget and risk gradings, not multiplicities: it is a
home for the algebra, not a free instance of it.

## What is retired

L1 and L2 were correct work against the wrong representation, and they are
why the defect was found at all. Under CARVe they become dead:

* `ctxLookupL` and the `CtxWellFormed` disambiguation invariant (L1)
* `linearSplitRoutes_holds` (L2)
* the linear-LEVEL migration across #125–#131

Two theorems are **kept deliberately** as regressions, so the inconsistent
pair cannot silently return under any future change:
`varL_linear_binders_are_indistinguishable` and
`shift_letTensor_reserves_two_slots`. `linearSplitRoutes_old_form_refuted`
is kept for the same reason.

## Staging

1. `CarveProto` landed under CI *(this PR)*
2. `Ctx` + `Mult` + `CJoin` in `DLC/Judgment.lean`; the 28 rules migrated
3. `DLC/Decidability.lean` — and re-derive, do not assume, the shipped
   checker's lookup behaviour
4. `DLC/CtxWellFormed.lean` — retire L1/L2, keep the regressions
5. Rust mirror + `spec/typing-rules.md` + `spec/syntax.md`; `check-drift.sh`
6. L3a re-proved over the new representation (the 26 proven cases largely
   survive and simplify), plus `boxI`'s `ClosedAbove` lemma — which is
   needed under *either* representation and is independent of this work
7. L3b, then L4

## Not adopted

*Leftover typing* (Zalakain & Dardha, *π with leftovers*, arXiv 2005.05902;
Agda, ~1850 LOC) threads an **output** usage context through judgments and
likewise avoids splits, parameterized over usage algebras covering shared,
graded and linear. Rejected as a worse fit for a de Bruijn setting with an
existing `shift`/`substAt` infrastructure; CARVe keeps the term datatype
unchanged, which this repo needs for the Aeneas-translated Rust mirror.

CARVe itself is **Rocq**, over Appel et al.'s MSL separation algebras with
Autosubst. We port the **design**, not the library: there is no MSL or
Autosubst here, and the resource algebra will be hand-rolled against the
existing `Quantale` trait.
