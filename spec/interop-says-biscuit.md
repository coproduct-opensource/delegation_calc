# Phase 2 — the interop bridge: `says` ↔ Biscuit / RFC 8693 / MCP (design)

**Status: design-first (this doc). No wire code yet** — per `CLAUDE.md` ("Tamarin model first, then
ProVerif cross-check, then wire format, then code"). This spec fixes the correspondence and the honest
fences before `models/tamarin/dlcd-interop.spthy` and the `dlc-interop` bridge crate.

## 0. Thesis

DLC-D's authorization core is the Abadi/Garg–Pfenning **`says` logic** (`Prop::Says`, `SpeaksFor`;
`Term::Sign`, `Verify`, `Delegate`, `Attenuate`), carried to deployed Rust and **machine-checked**:
`capability_safety` + `WellFormedLog` (`lean/DLCD/CapSafety.lean`), the runtime forgery-resistance of
`dlc-crypto::signed_term::verify_in_keyring` (Ed25519), and the verified admission checker
`rust_infer_sound`. The agent-identity ecosystem is independently converging on the **same shape** —
an append-only, offline-attenuable, signature-chained capability token — but **without the proofs**:

- **Biscuit** (Eclipse/Clever Cloud) — "an append-only list of blocks describing authorization
  properties," offline attenuation by appending a narrowing Datalog block, **Ed25519 signature
  chaining**. Validated by construction + tests, not a metatheorem.
- **IBCT** (Prakash 2026) — identity + attenuated authorization + provenance as an **append-only
  capability-token chain**, wire-encoded as Biscuit; validated empirically (600 attacks).
- **AIP** (arXiv 2603.24775) — Agent Identity Protocol for verifiable delegation across **MCP & A2A**;
  chained mode "inherits Biscuit's append-only block structure, Ed25519 signature chaining, and
  Datalog policy evaluation." Engineering artifact.
- **MCP OAuth 2.1 + PKCE** (2026), **RFC 8707** (Resource Indicators — audience binding), **RFC 8693**
  (token exchange — delegation). Specs, not proofs.

**The claim:** DLC-D is the *verified* kernel these systems approximate. `Term::Sign`/`Says` **is** the
credential Biscuit's blocks encode informally; `Delegate`/`Attenuate` **is** Biscuit attenuation;
`WellFormedLog` **is** the append-only chain invariant. Bridging them makes DLC-D's proofs available to
a deployed MCP/Biscuit stack, and makes DLC-D interoperable rather than a closed island.

## 1. The correspondence (grounded in the real API)

| DLC-D construct | Biscuit / JWT / MCP element | Correspondence property | Proof status |
|---|---|---|---|
| `Term::Sign(p, m, σ)` : `Says(p, φ)`  (`syntax.rs:65`) | a Biscuit **block** signed by `p`'s key, asserting fact `φ`; or a signed JWT with `iss = p` | issuer `p` vouches for `φ`; verified by `p`'s public key | **now** (typing: `rust_infer_sound` on the `Sign` arm ∈ F; crypto: `verify_in_keyring`, Tamarin/ProVerif-modelled) |
| `Term::Verify(p, m, σ)` (`syntax.rs:67`) | Biscuit signature verification of a block against `p`'s key | acceptance ⟹ `p` really signed | **now** (`signed_term::verify_in_keyring`) |
| `Term::Delegate` / `Attenuate` (`syntax.rs:70,72`) | **append a narrowing block** (offline attenuation) / RFC 8693 token exchange | the appended right is `⊑` the parent (attenuate-only) | terms exist; the "attenuate only narrows" metatheorem over `Deriv` is a **gap** (Phase 4) |
| `Prop::SpeaksFor(q, p)` (`syntax.rs:33`) | RFC 8693 token exchange (`q` may act as `p`); Biscuit block delegating `p`'s authority to `q` | `q ⇒ p` — `q`'s statements count as `p`'s | model-level (`sfExtract`/`delegate` arms in `decideLean`) |
| `WellFormedLog` (`CapSafety.lean:196`): `nil` \| `commit (h)(auth : Authorized c issuer)` | Biscuit's **append-only block list** (each block's checks must pass) / IBCT append-only token chain | a log/chain is well-formed iff every appended entry carries an authorization proof | **now** (inductive predicate; `capability_safety` reduces to it) |
| the command's sink/label `ℓ` (commit-I `command(M, c, ℓ)`) | **RFC 8707 audience binding** (`resource`/`aud` — which resource the token is valid for) | the credential is bound to one audience `ℓ`; cross-audience replay is rejected | model-level (IFC label = type index; runtime IFC is type-level, R2 finding) |

**Structural match, made precise.** `WellFormedLog log ++ [c]` requires `Authorized c issuer` for the
appended `c` — exactly Biscuit's rule that a new block may only *attenuate* (add checks), never widen.
The DLC-D side is an inductive Lean predicate with a machine-checked `capability_safety`; the Biscuit
side is the same shape enforced by Datalog evaluation at verify time. The bridge is a **faithful
encode/decode** between the two representations of one credential, not a re-derivation.

## 2. Honest fences

- **Interop is the largest NEW surface.** Bridging a *compile-time* `says`-credential to a *runtime*
  Biscuit/JWT token is real crypto-realization work; it is **partial-correctness** like the rest of the
  transport chain (the `ok`/no-overflow fences), and staged model-first.
- **Compile-time ↔ runtime gap.** DLC-D's Tier-2 certificate proves *typeability* (`rust_infer_sound`);
  the Ed25519 realization of the `says`-credential is the separate `dlc-crypto` layer. The bridge joins
  a *typed* credential to a *signed* token; it does not collapse the two guarantees into one.
- **Attenuate-only soundness is a Phase-4 gap.** The `Attenuate`/`Delegate` terms exist and Biscuit's
  attenuation is offline-narrowing by construction, but "`Attenuate` only narrows" as a metatheorem
  over `Deriv` is unproven (the terms are in `dlc-core`; the metatheorem is not).
- **Runtime IFC stays type-level.** The `ℓ`/audience axis is a build-time claim (a faithful label decode
  is provably impossible — R2); RFC 8707 audience binding is enforced at the token layer, not by
  DLC-D's decode.
- **No new `dlc-core` deps.** The bridge lives in a **new `dlc-interop` crate** (or extends
  `dlc-protocol`), never `dlc-core` — the Aeneas fence stays intact. Biscuit's `biscuit-auth` is a
  third-party dep, so it is confined to the bridge crate.

## 3. Staged plan (green-to-green, models before wire)

1. **This spec** — the correspondence + fences. ✅
2. **`models/tamarin/dlcd-interop.spthy`** (+ ProVerif cross-check) — the interop protocol is a *new*
   protocol, so it gets its own model with the same **anti-vacuity witness + differential-bite**
   discipline as `dlcd-replication.spthy`. 🔨 **STARTED** — root issuance + audience-bound verification
   proved (tamarin-prover 1.12.0, CI-gated in `tamarin.yml`): `cred_binds_issuer` (forgery-resistance:
   acceptance ⟹ genuine issuance, unless the issuer key is revealed), `no_cross_audience_replay`
   (RFC 8707: a credential issued for `aud1` is never accepted at `aud2 ≠ aud1`), `exec_accept`
   (non-vacuity), `attenuation_roots_in_issuance` (offline attenuation never fabricates a root the
   issuer never signed — Biscuit/DCC "authority monotonic narrowing"), `exec_attenuate` (attenuation
   non-vacuity) — **all 5 `verified`**. ✅ The differential BITE landed (`dlcd-interop-bite.spthy` + `scripts/check-tamarin-interop-bite.sh`, CI-gated): removing `AudienceBinding` makes `cross_audience_reachable` reachable while it is FALSIFIED in the guarded model — the audience check is machine-checked load-bearing. ✅ ProVerif cross-check landed (models/proverif/dlcd-interop.pv, CI-gated): both correspondences prove `is true`, accept events reachable; surfaced a real encoding difference (ProVerif `sign` is public ⟹ honest-issuer scoping; disequality audience form stays Tamarin-only).
3. 🔨 **`dlc-interop` bridge crate STARTED** (`crates/dlc-interop`) — a native CBOR interop token
   (`InteropToken{issuer, audience, term, sig}`) that embeds the proof term via `dlc_protocol::wire`
   VERBATIM (so the signed bytes are preserved). `encode_credential`/`decode_credential`/`verify_credential`
   (thin over `verify_in_keyring`); the KEY test `round_trip_preserves_verification` PASSES (a credential
   the verifier accepts still verifies after encode→decode) + tamper-fails + corrupt-decode-fails.
   `biscuit-auth` (the real Biscuit bytes) is confined to this crate as a follow-up; dlc-core/Aeneas
   untouched. Original spec of the bridge crate:

   **`dlc-interop` bridge crate** — `encode`/`decode` a `says`-credential (`Term::Sign` + Ed25519)
   to/from a Biscuit token, reusing `dlc-protocol::wire::{encode, decode}` **verbatim** for the embedded
   term (the `codec.rs` discipline), with a **round-trip-preserves-verification** test: a credential that
   `verify_in_keyring` accepts, encoded to a Biscuit and back, still verifies (and vice-versa for the
   attenuation edge).

## 4. Reading list (grounded)

- Biscuit spec — `github.com/eclipse-biscuit/biscuit` `SPECIFICATIONS.md`; `biscuitsec.org`.
- `biscuit-rust` — `github.com/eclipse-biscuit/biscuit-rust` (the dep the bridge would use).
- AIP — `arxiv.org/abs/2603.24775` (Biscuit chained delegation across MCP/A2A).
- MCP OAuth 2.1 + RFC 8707/8693 deep-dive — `kane.mx/posts/2025/mcp-authorization-oauth-rfc-deep-dive`.
- RFC 8707 audience binding for MCP — the `nhimg.org` workload-identity note.
- Vouchsafe (offline capability graph) — `arxiv.org/pdf/2601.02254`.

## 5. Verification gates (per stage)

- **This doc:** `scripts/check-claims.sh` + `check-spec-drift.sh` green if they gate specs (every claim
  cites a real theorem/API line or an honest fence — done above).
- **Model:** `tamarin-prover --prove dlcd-interop.spthy` + ProVerif green with the differential-bite gate.
- **Bridge crate:** round-trip-preserves-verification test; `cargo test`/`clippy -D warnings`/`fmt`;
  drift-clean (the bridge never touches `dlc-core`).
