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
## Runtime credential — the verify-then-authorize PEP (#18, LANDED)

`admit_joint` is the *typeability* half. The runtime *signature* half is
`crates/dlc-d/src/runtime.rs::admit(keyring, issuer, tool, sig)`: a real Ed25519
`verify_in_keyring` over a domain-separated **cap message** for `tool`, fail-closed. The tool is
bound to the grant by the signature covering `cap_atom(tool)` — FNV-1a of the tool name,
**byte-for-byte identical** to the macro's `atom_hash` (`dlc-d-macro/envelope.rs`), so the
compile-time `Cap<Invoke<Tool>, Issuer>` and the runtime credential name the SAME atom (the
compile-time↔runtime binding). Tests (green): a valid credential ADMITS its tool; the same signature
is REJECTED for a different tool, for a tampered signature, and for an unknown issuer (fail-closed,
right-reason). The `governed_agent` example calls `admit()` on its SendEmail path with a real
Ops-signed credential.

**The two guarantees are joined at the admission entry point, not collapsed:** the Lean side
(`admit_joint`) proves the envelope is a real `commit-I` derivation (typeability); `dlc-crypto` proves
the credential's signature (validity); `admit()` composes them — a tool invocation is admitted iff its
cap is typed (macro, compile time) AND the presented credential is genuinely signed for that tool
(runtime). Prior art: the 2026 verify-then-authorize / PEP idiom (Before-the-Tool-Call, arXiv
2603.20953; Sovereign Execution Broker, arXiv 2606.20520) — but credential-bound *and* backed by a
machine-checked typing theorem, not policy alone.

Fence: `admit()` is not yet proved EQUIVALENT to the type-checker path in Lean (that would relate the
signed cap atom to the `Deriv`'s cap prop); it is the runtime signature check that the typed cap's
*validity* rests on, joined at the entry point. `dlc-core`'s Aeneas fence is intact — `dlc-crypto` is a
`dlc-d` dependency, never `dlc-core`.

## Why this matters

The forward half is the one that carries the security guarantee an adopter cares about: **a
DLC-D-governed service cannot admit an action the model forbids** — proved, over all admission terms,
carried to the Aeneas-translated deployed checker. The remaining totality half is a liveness-flavoured
"the checker always produces a verdict" property whose only gap is mechanical Aeneas plumbing, honestly
marked for a later `Aeneas.step` pass (prior art: soundness = "accepts ⟹ correct", the safety
direction — Microsoft Research, *Automating Type Soundness Proofs via Decision Procedures*).
