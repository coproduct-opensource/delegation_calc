# DLC Typing Rules (Frozen — M1.Q1.a)

**Status:** Frozen at Week-1. Rule names are normative — Lean theorems and the
Rust verifier both refer to rules by these names.

The judgments:

```
Γ ⊢ M : φ                  -- logical typing
Γ ⊢ M ▷ M'                 -- small-step reduction
Γ ⊢_K M : φ                -- cryptographic typing under keyring K
```

`Γ` is a pair of an additive context Γ_A and a linear (multiset) context Γ_L.
We write `Γ_A; Γ_L ⊢ M : φ` when the distinction matters, and just `Γ ⊢ M : φ`
otherwise. The empty linear context is `∅`. Linear-context split is written
`Γ_L = Γ_L^1 , Γ_L^2`.

## 1. Structural rules

```
   x:φ ∈ Γ_A
─────────────────  (var-A)
Γ_A; ∅ ⊢ x : φ

────────────────────  (var-L)
Γ_A; x:φ ⊢ x : φ

Γ_A;  Γ_L      ⊢ M : φ
─────────────────────────────  (weaken-A)   [φ' irrelevant to M]
Γ_A, y:φ'; Γ_L ⊢ M : φ
```

Linear hypotheses do **not** admit weakening. The substructural restriction is
enforced by the multiset structure of `Γ_L`.

## 2. Logical connectives

```
Γ_A, x:φ; Γ_L ⊢ M : ψ
────────────────────────────  (imp-I)
Γ_A; Γ_L ⊢ λx:φ.M : φ ⊃ ψ

Γ_A; Γ_L^1 ⊢ M : φ ⊃ ψ      Γ_A; Γ_L^2 ⊢ N : φ
────────────────────────────────────────────────  (imp-E)
Γ_A; Γ_L^1, Γ_L^2 ⊢ M N : ψ
```

```
Γ_A; ∅ ⊢ M : φ      Γ_A; ∅ ⊢ N : ψ
────────────────────────────────────  (and-I)
Γ_A; ∅ ⊢ ⟨M, N⟩ : φ ∧ ψ

Γ_A; Γ_L ⊢ M : φ ∧ ψ
───────────────────────  (and-Eₗ)
Γ_A; Γ_L ⊢ π₁ M : φ
```

(Symmetric `and-Eᵣ`. Disjunction rules `or-I`, `or-E` symmetric to standard
intuitionistic logic.)

## 3. Linear connectives

```
Γ_A; Γ_L^1 ⊢ M : φ      Γ_A; Γ_L^2 ⊢ N : ψ
────────────────────────────────────────────  (tensor-I)
Γ_A; Γ_L^1, Γ_L^2 ⊢ M ⊗ N : φ ⊗ ψ

Γ_A; Γ_L^1 ⊢ M : φ ⊗ ψ      Γ_A, ; Γ_L^2, x:φ, y:ψ ⊢ N : χ
──────────────────────────────────────────────────────────  (tensor-E)
Γ_A; Γ_L^1, Γ_L^2 ⊢ let x⊗y = M in N : χ

Γ_A; Γ_L, x:φ ⊢ M : ψ
──────────────────────────  (lolli-I)
Γ_A; Γ_L ⊢ λx:φ.M : φ ⊸ ψ

Γ_A; Γ_L^1 ⊢ M : φ ⊸ ψ      Γ_A; Γ_L^2 ⊢ N : φ
────────────────────────────────────────────────  (lolli-E)
Γ_A; Γ_L^1, Γ_L^2 ⊢ M N : ψ
```

## 4. Affirmation (`says`)

```
Γ_A; Γ_L ⊢ M : φ      σ = Sign_{sk(p)}(canonical(M))
─────────────────────────────────────────────────────  (says-I)
Γ_A; Γ_L ⊢ ⟨M, σ⟩_p : p says φ

Γ_A; Γ_L^1 ⊢ M : p says φ      Γ_A, x:φ; Γ_L^2 ⊢ N : ψ
───────────────────────────────────────────────────────  (says-E)
Γ_A; Γ_L^1, Γ_L^2 ⊢ let ⟨x⟩_p = M in N : p says ψ
```

The `says-I` rule is the **load-bearing inference of T2**. The signature `σ`
is a witness of the underlying proof's existence under `p`'s key. Without
`σ`, no `says-I` step is derivable.

## 5. Speaks-for and delegation

```
Γ ⊢ M : p says (q ⇒ p)
─────────────────────────────  (sf-extract)
Γ ⊢ extract(M) : q ⇒ p

Γ ⊢ M : p says (q ⇒ p)         Γ ⊢ N : q says φ
──────────────────────────────────────────────────  (delegate)
Γ ⊢ delegate(M, N) : (p ⊓ q) says φ
```

**Design notes**

- `delegate` is the **chain-composition operator**. It produces a `p ⊓ q says`
  conclusion, which by associativity of `⊓` chains naturally: a sequence of
  delegations builds `H ⊓ A ⊓ B ⊓ C says φ`.
- Chain splicing (the RFC 8693 vulnerability) is impossible because the same
  `p` appears in *both* premises and the conclusion. A splice would require
  conjuring a `q says φ` from one delegation context and combining with
  `p says (q' ⇒ p)` from another — but then `q ≠ q'` blocks the rule.

## 6. Attenuation

```
Γ ⊢ M : p says φ      φ ⊃ ψ      ψ ≤_L φ
─────────────────────────────────────────  (attenuate)
Γ ⊢ attenuate(M, ψ) : p says ψ
```

The side condition `ψ ≤_L φ` (provability respects the IFC lattice) is what
prevents privilege escalation via attenuation. The `≤_L` relation is the
order on labels in `lean/DLC/IFCLabel.lean`.

## 7. IFC labels

```
Γ ⊢ M : φ
──────────────────────  (lift)
Γ ⊢ lift_ℓ(M) : φ @ ℓ

Γ ⊢ M : φ @ ℓ₁      Γ ⊢ N : (φ ⊃ ψ) @ ℓ₂
─────────────────────────────────────────────  (app-IFC)
Γ ⊢ M N : ψ @ (ℓ₁ ⊔ ℓ₂)

Γ ⊢ M : φ @ ℓ      Γ ⊢ π : DeclassifyPolicy(ℓ → ℓ')
────────────────────────────────────────────────────  (declassify)
Γ ⊢ declassify_ℓ'(M, π) : φ @ ℓ'
```

`app-IFC` propagates labels by lattice join — standard IFC. The novelty is
that this is *the same* application rule that drives delegation in `imp-E`, so
IFC and authorization compose by construction.

`declassify` requires an explicit declassification policy witness; this is the
seam where nucleus's `portcullis-core::DeclassifyProof` plugs in at M1.Q4.a.

## 8. Obligations

```
Γ ⊢ M : φ      Γ ⊢ N : O
──────────────────────────  (box-I)
Γ ⊢ box_O(M, N) : □_O φ

Γ ⊢ M : □_O φ      Γ ⊢ N : O      O is linear
────────────────────────────────────────────────  (discharge)
Γ ⊢ discharge(M, N) : φ
```

The `discharge` rule is the **only** elimination form for `□_O φ`. The side
condition "O is linear" enforces the one-shot semantics — an obligation
discharged once cannot be discharged again.

`box_O(M, N)` carries the obligation as a term index, matching the discipline
of `λ x:φ. M` and `lift_ℓ(M)`. Earlier revisions of this section wrote the
conclusion as `box(M, N)`, leaving `O` recoverable only from `N`'s type; the
term grammar (`spec/syntax.md`) omitted the production altogether, and
`lean/DLC/Judgment.lean`'s `Deriv.boxI` consequently concluded at
`Term.app M N` — reusing application, so no obligation ever reached the
syntax. That is the root cause of T4's vacuity: `pendingObligations` reads
terms, and no term could carry an obligation. See
`spec/t4-obligation-design-2026-07.md` for the R0–R6 remediation ladder.

The Lean and Rust encodings still conclude at `Term.app` as of this
revision; R2/R3 bring them into line with the rule above. Until then the
spec is deliberately ahead of the encodings — the staging that
`check-spec-drift.sh` explicitly tolerates.

## 9. Time

```
α is a verifiable anchor commitment with α.epoch < τ
─────────────────────────────────────────────────────  (now)
Γ ⊢ now(τ, α) : ⊤ @ {fresh}     -- proof that "now < τ"

Γ ⊢ M : φ      Γ ⊢ N : ⊤ @ {fresh}     -- N is a now-proof
──────────────────────────────────────────────────────────  (within-I)
Γ ⊢ within(M, τ) : ◇_τ φ

Γ ⊢ M : ◇_τ φ      now < τ at verify-time
─────────────────────────────────────────────  (within-E)
Γ ⊢ openWithin(M) : φ
```

Time anchor verification (`α`) is concrete; for drand the verifier checks the
group BLS signature on the round. The exact realization is in
`crates/dlc-crypto/src/time_anchor.rs`.

## 10. Cryptographic typing — `⊢_K`

The bridge judgment. For every rule of `⊢`, there is a corresponding rule of
`⊢_K` that additionally checks signatures against the keyring. The pivotal
rule:

```
σ verifies under K.lookup(p) on canonical(M)
                  Γ ⊢_K M : φ
─────────────────────────────────────────────────  (verify)
Γ ⊢_K ⟨M, σ⟩_p : p says φ
```

**T2, target form** (OPEN — this is the intended theorem, not a proven
one): for every `K` extractable from `Γ`,

```
                Γ ⊢ M : φ    ⇔    Γ ⊢_K M : φ
```

**Status (2026-07 audit):** the unqualified iff is NOT proven, and an
earlier attempt to axiomatize its forward direction was refutable
in-system (machine-checked in `lean/DLC/Witness/AxiomAudit.lean`).
What IS proven, axiom-free, is the symbolic characterization for the
propositional fragment (`lean/DLC/Correspondence.lean`):

```
     Γₐ ⊢_K M : φ    ⇔    Γₐ ⊢ M : φ  ∧  allSigsVerify K M
```

The EUF-CMA reduction that the target form's reverse direction needs
does not yet exist: the EasyCrypt L2.4 file is a skeleton whose
placeholder axiom encodes nothing. See `lean/theorem-status.json` for
the tracked open obligations.

## 11. Reduction

Small-step, deterministic (implemented as a partial function). Head
redexes:

```
(β)             (λx:φ.M) N           ▷  M[N/x]
(and-Eₗ-β)      π₁ ⟨M, N⟩            ▷  M
(and-Eᵣ-β)      π₂ ⟨M, N⟩            ▷  N
(or-E-β)        case (inl M) of …    ▷  left[M/x]   (inr symmetric)
(let-tensor)    let x⊗y = M⊗N in P   ▷  P[M/x, N/y]
(says-extract)  let ⟨x⟩_p = ⟨M, σ⟩_p in N
                                     ▷  N[M/x]
(sf-extract-β)  sfExtract(⟨M, σ⟩_p)  ▷  M
(delegate-β)    delegate(⟨M, σ⟩_p, ⟨N, σ'⟩_q)
                                     ▷  ⟨N, σ'⟩_{p⊓q}     -- σ checked by ⊢_K, not here
```

**Congruence (evaluation contexts), 2026-07.** When the head rule for
an elimination form does not yet fire, reduction descends into the
scrutinee/function position — call-by-name, one deterministic
position per form:

```
(ξ-app)        M ▷ M'  ⇒  M N ▷ M' N            -- M not a λ
(ξ-fst/snd)    M ▷ M'  ⇒  πᵢ M ▷ πᵢ M'           -- M not a pair
(ξ-case)       M ▷ M'  ⇒  case M of … ▷ case M' of …
(ξ-lettensor)  M ▷ M'  ⇒  let x⊗y = M in P ▷ let x⊗y = M' in P
(ξ-letsays)    M ▷ M'  ⇒  let ⟨x⟩_p = M in N ▷ let ⟨x⟩_p = M' in N
(ξ-sfextract)  M ▷ M'  ⇒  sfExtract M ▷ sfExtract M'
(ξ-delegate)   left position first, then right once left is a ⟨…⟩_p value
```

Without these, nested eliminations are stuck (`π₁ (π₁ ⟨⟨a,b⟩,c⟩)` had
no reduct) and progress fails; see
`spec/t3-two-run-design-2026-07.md` (FINDING, 2026-07-02).

**Frozen forms.** `verify`, `attenuate`, `declassify`, `discharge`,
`liftLabel`, `withinIntro` do not reduce and have no congruence rule:
they are checked by the verifier (`⊢_K` / IFC / obligation layers)
rather than computed. In particular `attenuate-β` (reproof) and
`discharge-β` are NOT implemented — discharge-β awaits the
obligation-carrying constructor (T4 non-vacuity package), and
attenuate's reproof is a verifier-side notion. The earlier version of
this section listed them as reduction rules; that overstated the
semantics.

**Values (computational core).** `λ`, `⟨M,σ⟩_p`, `⟨M,N⟩`, `inl/inr`,
`M⊗N`, `now`, plus the frozen forms above. **Progress** holds for
closed well-typed terms of the computational core (no frozen
eliminations): such a term is a value or steps. Mechanized as the
rung-3b-0 witness (`lean/DLC/Progress.lean`).

**Subject reduction** (M1.Q2.c): if `Γ ⊢ M : φ` and `Γ ⊢ M ▷ M'`, then
`Γ ⊢ M' : φ`. Proven for the propositional fragment
(`propDeriv_subject_reduction`), including the congruence cases;
linear context bookkeeping is the load-bearing part of the full-`Deriv`
extension (open).

## 12. Rule index

For cross-reference from Lean (`DLC.RuleName`) and Rust (`dlc-core::RuleName`):

| ID | Rule | File ref |
|---|---|---|
| `var-A` | additive variable | §1 |
| `var-L` | linear variable | §1 |
| `weaken-A` | additive weakening | §1 |
| `imp-I` / `imp-E` | implication | §2 |
| `and-I` / `and-Eₗ` / `and-Eᵣ` | conjunction | §2 |
| `or-I` / `or-E` | disjunction | §2 |
| `tensor-I` / `tensor-E` | linear conjunction | §3 |
| `lolli-I` / `lolli-E` | linear implication | §3 |
| `says-I` / `says-E` | affirmation | §4 |
| `sf-extract` | speaks-for | §5 |
| `delegate` | chain composition | §5 |
| `attenuate` | macaroon caveat | §6 |
| `lift` / `app-IFC` / `declassify` | IFC | §7 |
| `box-I` / `discharge` | obligations | §8 |
| `now` / `within-I` / `within-E` | time | §9 |
| `verify` | cryptographic bridge | §10 |
| `β` / `let-tensor` / `says-extract` / `delegate-β` / `attenuate-β` / `discharge-β` / `within-β` | reduction | §11 |

Approximately 40 rules total. The Lean encoding (`lean/DLC/Judgment.lean`)
implements one constructor per row; the Rust mirror exposes them as variants
of the verifier's case analysis in `dlc-verifier/src/check.rs`.
