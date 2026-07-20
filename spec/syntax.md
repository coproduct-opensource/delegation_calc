# DLC Syntax (Frozen — M1.Q1.a)

**Status:** Frozen at Week-1. Any non-cosmetic change requires (a) a corresponding
update to `spec/typing-rules.md`, (b) the affected Lean modules, (c) the Rust
mirror in `dlc-core/src/syntax.rs`, and (d) a passing Aeneas regeneration.

This file is the source of truth for the grammar. The Lean encoding
(`lean/DLC/Syntax.lean`) and the Rust mirror (`crates/dlc-core/src/syntax.rs`)
both follow this document.

---

## 1. Syntactic categories

```
Atoms              a, b, c ∈ AtomTable           (atomic propositions)
Principal ids      h ∈ PrincipalId               (32-byte SHA-256 of SPIFFE-ID)
Capability indices i ∈ ℕ                         (IFC label coordinates)
Action ids         α ∈ ActionId                  (opaque obligation tags)
Time bounds        τ ∈ ℕ                         (ms since UNIX epoch)
Algorithm ids      γ ∈ {0=Ed25519, …}            (signature algorithms)
Signature bytes    σ ∈ Bytes                     (raw signature)
```

## 2. Principals

```
p, q, r ::= h                       atom: identified by SPIFFE-ID hash
          | p ∧ q                   conjunctive: both consent
          | p ∨ q                   disjunctive: either consents
          | p ⊓ q                   acting: p acting in q's capacity
```

**Design notes**

- `⊓` is **associative but NOT commutative**. `H ⊓ A ⊓ B` parses left-
  associatively as `(H ⊓ A) ⊓ B` and reads "B acting as A acting as H." Chain
  semantics — which RFC 8693 fudges as opaque transitive closure — gets a
  first-class associative operator here.
- `∧` and `∨` are commutative and idempotent; `⊓` is neither.
- `k(p)` from §2.1 of the design spec is not a separate constructor; it is
  the projection `Principal::key_id` that resolves an atomic principal to its
  algorithm-tagged public key via the keyring. Composite principals do not
  have keys themselves — only their atomic constituents do — so `k(p ⊓ q)` is
  *not* well-defined.

## 3. Labels and obligations

```
ℓ        ::= ⟨i₁, …, iₙ⟩         IFC label (Week-1: sorted-deduped list;
                                  M1.Q4.a: 13-dim PermissionLattice)

O, O' ::= ⊤ | ⊥                  trivially / un-dischargeable
        | act_of(p, α)            principal p must perform action α
        | within(τ)               must discharge before time τ
        | O ⊗ O'                  both due (linear; consumed once)
        | O ⊸ O'                  if O discharged, O' becomes due
```

**Design notes**

- Obligations are **linear**. `O ⊗ O'` is multiplicative ("must do both");
  `O ⊸ O'` is linear implication. Discharge consumes a hypothesis.
- The lattice operations on labels (`⊓`, `⊔`, `→`) live in
  `lean/DLC/IFCLabel.lean`. At Week-1 we use a placeholder; M1.Q4.a swaps in
  nucleus's `PortcullisCore.PermissionLattice` so the 13 capability dimensions
  become the production label structure.

## 4. Propositions

```
φ, ψ ::= ⊤ | ⊥                   trivial / absurd
       | a                       atomic
       | φ ⊃ ψ                   implication (additive)
       | φ ∧ ψ | φ ∨ ψ            additive conjunction / disjunction
       | p says φ                affirmation modality
       | p ⇒ q                   speaks-for
       | φ @ ℓ                   IFC label
       | □_O φ                   obligation-attached
       | ◇_τ φ                   time-bounded
       | φ ⊗ ψ                   multiplicative (linear) conjunction
       | φ ⊸ ψ                   linear implication
```

**Design notes**

- `p says φ` is the Garg-Pfenning affirmation modality. Reflexive and
  transitive in the right adjoint of the principal-id lattice.
- `p ⇒ q` is `p` *speaks for* `q`: `(p says φ) ⊃ (q says φ)` is derivable.
- `φ @ ℓ` annotates the IFC label at which `φ` is taken to hold. Lattice join
  on application (`app-IFC` rule in typing-rules.md).
- `□_O φ` says "to use this proof of `φ`, you must discharge `O`."
- `◇_τ φ` says "you must use this proof of `φ` before time `τ`." Time anchor
  proofs (drand / NIST beacon) realize the side condition `now < τ`.
- The linear connectives `⊗` and `⊸` enable resource-style accounting for
  proofs that must be used exactly once — load-bearing for the DP-budget
  obligation form (`□_{ε-DP(δ)} φ` of §4.3 in the design spec).

## 5. Proof terms

```
M, N ::= x                             variable (de-Bruijn index)
       | λ x:φ. M                      lambda
       | M N                           application
       | ⟨M, σ⟩_p                      sign: introduces p says φ
       | verify_p(M, σ)                check signature; eliminates p says
       | delegate(M, N)                build (p ⊓ q) says φ from (q⇒p) + (q says φ)
       | attenuate(M, ψ)               weaken affirmation along provable implication
       | saysBind_p(M, N)              let ⟨x⟩_p = M in N — says-E (§4)
       | box_O(M, N)                   attach obligation O to a proof of φ
       | discharge(M, N)               consume obligation O to extract φ
       | lift_ℓ(M)                     IFC label introduction
       | declassify_ℓ(M, π)            controlled label lowering
       | now(τ)                        time anchor proof of now < τ
       | within(M, τ)                  ◇_τ introduction
```

**Design notes**

- Variables are de-Bruijn indices: no name capture issues in `subst`. Hand-
  written Lean and Aeneas-translated Lean agree on representation.
- `⟨M, σ⟩_p` carries a signature `σ` of `canonical_bytes(M)` under principal
  `p`'s key. **The proof term for `p says φ` is intrinsically the pair of the
  underlying proof and a signature.** This is what fuses the logic with the
  cryptography — `says-I` cannot exist without a signature, and the signature
  cannot exist without proving `M : φ` first.
- `delegate(M, N)` is the chain-composition operator. Its type rule is the
  load-bearing inference for multi-hop delegation; chain splicing (the RFC
  8693 vulnerability) is impossible because `M`'s principal must match `N`'s
  exactly, and the type system enforces this at every step.
- `attenuate(M, ψ)` is the macaroon caveat operation, lifted to the calculus.
  Crucially, the type rule requires `ψ ≤_L φ` in the IFC lattice — you cannot
  "attenuate" a low-integrity statement into a high-integrity one.
- `saysBind_p(M, N)` is the term for **says-E** (`spec/typing-rules.md` §4),
  written `let ⟨x⟩_p = M in N` there. It BINDS `x:φ` in `N`, so it is a real
  binder: `shift`/`substAt` bump the cutoff by one under `N`. The conclusion
  PRESERVES the modality (`p says ψ`), which is what distinguishes it from a
  plain elimination.

  **This production was missing from the grammar** until 2026-07-20, exactly
  as `box_O` was — §4 stated the rule with a let-binder term while the
  grammar had no production for it, so the Lean encoding concluded at
  `Term.app M N` instead. `Term.app` is not a binder, so `shift` never bumped
  the cutoff for `N`, and the says-E case of any shift/substitution lemma was
  unprovable (off by one). See `spec/linear-substitution-design-2026-07.md`.

  **Anomaly, recorded not resolved:** `lean/DLC/Judgment.lean` also carries a
  `letSaysE` rule with the SAME premises but a conclusion that STRIPS the
  modality (`ψ` rather than `p says ψ`). That rule appears nowhere in this
  spec's rule index (§13) and uses `Term.letSays`. Whether it should be
  specced or removed is open; it is not part of the says-E fix.

- `box_O(M, N)` is the introduction form for `□_O φ`: `M` proves `φ`, `N` is
  the obligation evidence. **The obligation `O` is carried by the term, not
  only by the typing derivation.** This follows the annotation discipline
  already used by `λ x:φ. M`, `lift_ℓ(M)`, `declassify_ℓ(M, π)` and
  `within(M, τ)` — the index is part of the syntax. It is what makes
  `pendingObligations : Term → List Obligation` (T4) a function of syntax
  alone; recovering `O` from `N`'s type instead would force T4 to quantify
  over derivations rather than terms.
- `discharge(M, N)` is the only way to consume a `□_O φ`. There is no other
  elimination form — obligations cannot be silently dropped.
- `now(τ)` is the seam where the time anchor lives. It is a *proof* that
  `now < τ`, not a runtime check; the verifier confirms the embedded anchor
  commitment is well-formed (e.g., a drand round signature) and that the
  round's epoch is < `τ`.

## 6. Canonical encoding

The canonical bytes used for signing follow this informal rule (formalized in
`crates/dlc-crypto/src/signed_term.rs` and round-tripped against
`crates/dlc-protocol/src/wire.rs`):

```
canonical(t : Term) = CBOR(
  tag = OperationTag(t),
  type = canonical(typeOf(t)),
  children = [content_hash(canonical(c)) for c in subterms(t)],
  metadata = { label, obligations, timestamp, nonce }
)
```

Each subterm is referred to by **content hash**, so the canonical bytes form a
Merkle DAG and changing one leaf changes only the path-to-root hashes
(selective recomputation, §3.1 of the design spec).

## 7. Reserved-for-future / explicitly out of scope

- **Higher-order quantification** is out of scope. DLC is propositional +
  modal + linear + temporal; first-order quantification over principals would
  break T1 decidability. The design hovers above MSO + MTL in expressiveness.
- **Mutually recursive types** are out of scope (Aeneas-unfriendly).
- **Polymorphism over labels** is reserved for v2 of the spec. Phase-1 uses
  monomorphic label parameters everywhere.

## 8. ABNF

The wire ABNF lives in `spec/abnf.md` and is derived from §6's canonical
encoding. IETF draft `draft-crisp-dlc-token` is the normative source once
Phase-4 begins.
