# Joint admission control — the deployed check IS the model (design + status)

The program's biggest asterisk was that "carried to deployed Rust" held only in *pieces*: the macro's
Tier-2 cert proves **typeability** (`rust_infer_sound`), `dlc-crypto` proves **signature validity**
(`verify_in_keyring`), and the Aeneas transport proves **refinement under `ok`** — but no single
statement said *the running admission decision equals the model's authorization decision*. This arc
closes that on the **admission fragment** (`AdmitFrag` — the one term shape
`#[dlc_d::agent_service]` emits: `Lam (Atom c) (Var 0) : Atom c ⊃ Atom c`).

## What is proved (`lean/DLC/AdmitFrag.lean`, `⊆ [propext, Classical.choice, Quot.sound]`)

- **`admitFrag_propFrag`** — `AdmitFrag ⊆ PropFrag`: every admission term lies in the agreeing
  fragment `rust_infer_sound` covers.
- **`admit_infer_var0` / `admit_store_total`** (#16) — the store lookup `decide.infer E (Var 0) =
  ok (some (Atom c))` in the body context `[Atom c]`: the **substantive** totality (a context lookup
  — the one place a checker returns `none`/fail on real input).
- **`admit_joint`** (#17, ★) — **JOINT ADMISSION SOUNDNESS, forward direction, UNCONDITIONAL:** if the
  deployed checker admits (`decide.infer emptyCtx t = ok (some inferred)`), then
  `Nonempty (Deriv (decCtx emptyCtx) (decTerm t) (decProp inferred))` — a real derivation in the
  verified calculus. **The running admission decision is backed by the model: no false admits.** This
  is the security-load-bearing half — the kernel never grants a tool invocation the calculus would not
  type. The `ok` premise is not an assumption at the deployed site: it is exactly the fact the macro's
  compile-time `assert!(decide_pure …)` enforces (the cert test panics otherwise).

## What is NOT yet proved (honest fences)

- **The totality / `⟸` half** — *the checker ALWAYS admits* (so the `ok` premise is discharged
  in-Lean without observation) — rests on the `Lam`-wrapper totality **fenced in #16**. The
  substantive lookup is proved (`admit_infer_var0`); the surrounding Aeneas monadic plumbing
  (`clone` the ctx → `cons_a` the cap atom → `branch` on `some`) has no logical failure mode
  (`clone` is identity, `cons_a` is `push`+`extend_from_slice` on a one-element vector, well under
  `Usize.max`; `branch (some _)` is `Continue`), but its raw `ok`-reduction fought the version-specific
  `Aeneas.step`/`progress` tactic and is deferred. So: **accept ⟹ typable is unconditional; always-accepts
  is pending a mechanical wrapper step.**
- **Fragment scope.** `AdmitFrag` is the *current* macro shape (identity store-transformer). Richer
  admission envelopes (non-trivial store transformers, multi-cap) extend `AdmitFrag` and re-run the
  same composition.
- **Runtime credential (#18, pending).** `admit_joint` is about the type-checker path; wiring the real
  `verify_in_keyring` signature check into the admission call path (so the equivalence is about the
  actual deployed decision, not only typeability) is the next increment.

## Why this matters

The forward half is the one that carries the security guarantee an adopter cares about: **a
DLC-D-governed service cannot admit an action the model forbids** — proved, over all admission terms,
carried to the Aeneas-translated deployed checker. The remaining totality half is a liveness-flavoured
"the checker always produces a verdict" property whose only gap is mechanical Aeneas plumbing, honestly
marked for a later `Aeneas.step` pass (prior art: soundness = "accepts ⟹ correct", the safety
direction — Microsoft Research, *Automating Type Soundness Proofs via Decision Procedures*).
