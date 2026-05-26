# DLC Threat Model

**Status:** Draft v0.1. **Gates the Tamarin model** (L2.1) — no protocol model is
written until this document is reviewed and signed off by Cas Cremers (target:
M2.M7). Risk R-A3 ("Tamarin model and DLC disagree on adversary capabilities")
is *the* risk this document mitigates.

The single most important question this document answers: *what is the adversary
allowed to do, and what does the calculus assume?* A mismatch between the
calculus's implicit adversary and the Tamarin model's explicit Dolev-Yao one
invalidates §4.4 and T2.

---

## 1. Adversary model — Dolev-Yao with named exceptions

The adversary is **Dolev-Yao** (DY) plus the standard symbolic-model assumptions:

- **Full network control.** The adversary observes, drops, reorders, replays,
  and injects arbitrary messages on every channel between honest principals.
- **Polynomially-bounded computation** in the symbolic model; **EUF-CMA-secure
  signatures** in the computational model (the EasyCrypt L2.4 bridge).
- **Perfect cryptography in symbolic abstraction.** Hash functions are
  collision-resistant; encryption is IND-CPA where relevant; signatures
  cannot be forged without the secret key. The computational bridge L2.4
  discharges the gap to bit-level adversaries for the signature scheme.
- **Static corruption.** The adversary may corrupt a polynomial-bounded set
  of principals *at protocol start* and obtain their secret keys. **Adaptive
  corruption is out of scope for Phase-1.** Reason: adaptive corruption blows
  up Tamarin proof times by 10–100×; once T2 is closed for static, adaptive
  becomes a Phase-2-stretch deliverable rather than a blocker.
- **No side channels.** Timing, power, EM, cache, fault injection — all out
  of scope. The calculus assumes secret-key-bearing principals execute in
  side-channel-immune environments. In practice this is the role of
  nucleus's Firecracker microVM substrate, which is itself the subject of
  separate side-channel analysis.

The adversary **cannot**:

- Forge signatures of honest principals (computational L2.4 / symbolic Tamarin).
- Compute preimages under SHA-256 (collision resistance).
- Predict drand or NIST randomness-beacon values before publication (trusted
  beacons; if compromised, `◇_τ` proofs are invalidated — R-A4 mitigation).
- Compromise the transparency log's append-only history (witnessed roots are
  cosigned by a quorum; details in §4 below).

## 2. Principals: honest, corrupted, partially-trusted

Three trust states per atomic principal at protocol start:

- **Honest** — keys uncompromised; signatures and decisions are authoritative.
- **Corrupted** — adversary holds the secret key. All `says-I` decisions are
  attacker-controlled.
- **Quarantined** — known-corrupted at *some* point in history but with a
  verifiable "key compromise" event. Pre-quarantine signatures stand;
  post-quarantine signatures are rejected. This is the case the transparency
  log handles.

Composite principals (`p ∧ q`, `p ∨ q`, `p ⊓ q`) inherit trust as the lattice
meet of their components for `∧` and `⊓`, and as the join for `∨` (the most
generous reading: if either consents, the disjunctive principal acts).

## 3. Channel and key-distribution assumptions

- Every atomic principal has a stable public key obtainable via a JWKS-style
  endpoint over **plain HTTPS**. The verifier fetches the keyring at start
  and may cache it.
- Keys may rotate. Rotation events are signed by the principal's prior key
  and posted to the transparency log. The verifier checks rotation chains.
- The verifier itself is **not trusted** to be online. Once it has the
  keyring and the witnessed transparency-log root, it operates fully offline.
- Time is provided by drand or the NIST randomness beacon. The verifier
  treats these as **trust anchors**; their compromise breaks `◇_τ` (R-A4).

## 4. Transparency log assumptions

DLC's revocation story relies on a Merkle-tree transparency log:

- The log is append-only and the current root is **co-signed by a quorum of
  witnesses**. The verifier trusts a root that meets a quorum threshold
  configurable per deployment.
- Revocation = non-inclusion proof against a witnessed root. The verifier
  checks the proof offline once it has the root.
- The log carries:
  (a) Key rotation events (§3).
  (b) Explicit revocation entries: `p says ¬(q ⇒ p)` propositions, signed.
  (c) Content-hashes of issued proof terms (so a third party can verify
      "this proof was issued at time t").

The log is **untrusted to remain available**, but trusted to remain
**consistent** through the witness quorum. Loss of availability degrades
freshness, not soundness.

## 5. What the calculus assumes (implicit DY)

Where DLC's typing rules implicitly invoke the DY adversary:

- `says-I` assumes the signature `σ` is unforgeable without the private key
  of `p`. The symbolic model treats it as a primitive; L2.4 reduces it to
  EUF-CMA.
- `verify` in `⊢_K` assumes the public-key lookup `K.lookup(p)` is correct.
  Key rotation is handled by interpreting `K` as time-indexed (verifier picks
  the key valid at the proof term's `timestamp` metadata).
- `delegate` assumes the rule `p says (q ⇒ p)` was honestly produced by `p`.
  If `p` is corrupted, any `q` can be made a speaker-for; this is the design
  intent (delegation is a principal's prerogative).
- Transparency-log non-inclusion is the only revocation mechanism. If the log
  is compromised (consistency, not availability), revocation guarantees fail
  but `says-I`/`verify` soundness still holds.

## 6. What is OUT of scope

For Phase-1 closure:

- **Adaptive corruption.** Phase-2 stretch.
- **Anonymous credentials / zero-knowledge proofs.** Phase-3+ extension; the
  `Signature` type in `dlc-core::syntax` is parameterized to allow future
  zk-SNARK signatures, but the typing rules treat all algorithms uniformly.
- **Quantum adversaries.** Out of scope; Ed25519 is broken under Shor. A
  post-quantum DLC is the v2 of the artifact.
- **Side channels.** Per §1.
- **Denial-of-service.** The verifier's complexity bound (T1: O(|M|·log|Γ|))
  is what limits DoS, but a malicious *issuer* can still mint giant proof
  terms; rate-limiting at the issuance layer is out of scope.
- **Network confidentiality.** DLC proof terms are intended to be public; if
  a deployment wants confidentiality, it wraps DLC in TLS or similar — not a
  property of the calculus.

## 7. Properties the calculus must satisfy under this model

Stated as Tamarin lemma targets, to be filled in by Phase-2:

- **Auth(p, q, φ)** — for every trace in which a verifier accepts
  `(p ⊓ q) says φ`, there exists an earlier trace point at which `p`
  affirmed `(q ⇒ p)` and `q` affirmed `φ` (assuming neither corrupted).
- **Secrecy(k)** — for every honest `p`, the adversary never learns
  `sk(p)`.
- **Freshness(n)** — every nonce introduced by `now` is fresh and
  unforgeable.
- **NonSplicing** — there is no trace in which a `(p ⊓ q) says φ` derivation
  is accepted without a valid `q says φ` from the same delegation context.
  This is the formal statement of "no chain splicing."

These four become the load-bearing Tamarin lemmas. T2 in Lean reflects them.

## 8. Modeling choices made for the L2.1 Tamarin bootstrap

These are the design choices made in `models/tamarin/dlc.spthy` at L2.1
bootstrap (Phase-2 entry). Each is a decision Cremers's M2.M7 review will
either ratify or revise.

1. **Equational theory.** Default `signing` builtin only. drand BLS
   aggregation and VDF anchors are NOT modeled at L2.1 — `◇_τ` is treated
   as a freshly-produced principal-bound nonce. Adding the BLS equational
   theory is a follow-up if Cremers prefers it for the time-bound proofs.
2. **No restrictions yet.** The bootstrap model relies on the
   signature-pattern-match in `Delegate_Accept` to enforce
   no-chain-splicing. A `restriction Unique_Signature` may be needed once
   we add Says-rule weakening to permit repeated affirmations.
3. **Auto-sources is left on.** If `tamarin-prover --prove` reports
   incomplete proofs that auto-sources can't close, hand-written source
   lemmas land as a follow-up commit.
4. **Static honest set.** `LtkReveal` events fire only at the trace
   start; we do NOT model adaptive corruption (per §1 of this doc).
5. **Proposition as fresh nonce.** The wire form of a says-token contains
   the proposition; we model the proposition as a fresh symbolic value
   (`Fr(~prop)`). The DLC proof term is abstracted away — its content is
   irrelevant for the symbolic security properties (Auth, Secrecy,
   NonSplicing). The proof-of-φ structure is what Lean's `Deriv` models;
   the wire form is what Tamarin models.

## 9. Tamarin model — L2.1 sign-off checklist

The `models/tamarin/dlc.spthy` model encodes four properties matching §7.

- [x] **Secrecy of long-term keys** — `lemma secrecy_ltk`.
- [x] **Authentication of Says** — `lemma auth_says`.
- [x] **NonSplicing of delegation chains** — `lemma non_splicing` (the
      load-bearing property).
- [x] **Executability sanity check** — `lemma exec_delegation`.
- [ ] Reviewed by Cas Cremers (target M2.M7).
- [ ] ProVerif cross-check (`models/proverif/dlc.pv`) — L2.2.
- [ ] EasyCrypt computational bridge (`models/easycrypt/Game.eca`) — L2.4.
