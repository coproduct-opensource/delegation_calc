# DLC-D as the verified admission conjunct for nucleus / portcullis-core (integration design)

**Status:** DESIGN. This document specifies how `dlc_d::runtime::admit` (the verify-then-authorize PEP,
committed `1b82a4b`) plugs into `nucleus`'s `portcullis-core` reference monitor as a *cryptographic,
proof-carrying* admission check. It is a **PR proposal against nucleus, not an edit** — per `CLAUDE.md`,
nucleus is an upstream library; DLC-D does not modify it. Nothing here changes nucleus; the DLC-D side
(the [`dlc_d::admission`](../crates/dlc-d/src/admission.rs) facade) is the only code landed with it.

## 1. The gap in portcullis-core's admission checkpoint

`portcullis-core` already has an admission checkpoint — `manifest::check_admission(manifest) ->
AdmissionVerdict` (`crates/portcullis-core/src/manifest.rs`). It is **structural**: seven rules over
declared manifest fields (capabilities non-empty; remote-fetch vs. unlabeled instruction sources;
external sinks; trusted-output-from-remote; directive authority; …). Its own docstring names the
limit:

> **Limitation**: This checks the manifest, not the tool's behavior. A tool that lies in its manifest
> will pass admission.

`check_admission_with_policy(.., ManifestPolicy::RequireSigned)` adds a signature gate, but it checks
`manifest.is_signed()` — that the *manifest document* is signed — not that a specific caller holds an
*issuer-bound capability for this specific tool*. There is no cryptographic answer to "is THIS invocation,
by THIS principal, of THIS tool, authorized by an issuer we trust?" — and no admission verdict backed by
a machine-checked theorem.

That is exactly the conjunct DLC-D supplies.

## 2. What DLC-D contributes

`dlc_d::admission` (a thin, dependency-free facade over `runtime::admit`):

```rust
pub enum Decision { Admit, Deny(&'static str) }
pub fn decide(keyring: &KeyRing, issuer: &Principal, tool: &str, sig: &Signature) -> Decision;
pub fn cap_atom(tool: &str) -> u32;   // FNV-1a; byte-identical to the macro's atom_hash
pub use crate::runtime::{admit, AdmitError};
```

`decide(...)` returns `Admit` **iff** `issuer` genuinely signed a capability granting `tool` — a real
Ed25519 `verify_in_keyring` over the tool's domain-separated cap message — and fails closed otherwise
(bad signature / unknown issuer / credential minted for a different tool). Two properties make this more
than "another signature check":

- **Compile-time ↔ runtime binding.** `cap_atom(tool)` is FNV-1a of the tool name, **byte-for-byte
  identical** to what `#[dlc_d::agent_service]` computes at macro time (`dlc-d-macro/envelope.rs::
  atom_hash`). The type-level `Cap<Invoke<Tool>, Issuer>` the compiler checks and the runtime credential
  `decide` admits **name the same atom**. A credential for tool A provably cannot admit tool B.
- **Proof-carrying admission.** On the admission fragment (`AdmitFrag` — the identity store-transformer
  the macro emits), a positive admission is backed by `admit_joint` (`lean/DLC/AdmitFrag.lean`,
  `⊆ [propext, Classical.choice, Quot.sound]`): *if the deployed checker admits, a real `commit-I`
  derivation exists in the verified calculus.* **No false admits.** ACP model-checks its admission
  invariant offline; IBCT tests 600 attacks empirically; this carries a proof to the deployed check.

Cost is not the bottleneck: `decide` ≈ **19.5 µs/call** (measured, aarch64 release, `ed25519-dalek`;
`spec/joint-admission.md` §benchmark) — one Ed25519 verify plus a sub-nanosecond FNV, orders of
magnitude below agent tool-call timescales.

## 3. The integration point: a `PolicyCheck`

`portcullis-core::combinators` already defines the composition seam:

```rust
pub trait PolicyCheck: Send + Sync {
    fn check(&self, req: &PolicyRequest) -> CheckResult;   // Allow | Deny(String) | RequiresApproval | Abstain
    fn name(&self) -> &str;
}
```

DLC-D admission becomes one more `PolicyCheck`, composed with the manifest rules via the existing
`AllOf` combinator (most-restrictive-wins via `CheckResult::meet`). The adapter lives **on the nucleus
side** (it needs portcullis-core's trait); it is ~15 lines and maps `Decision` → `CheckResult` directly:

```rust
// PROPOSED, in nucleus (e.g. crates/portcullis/src/says_admission.rs) — NOT landed here.
use dlc_d::admission::{decide, Decision};
use dlc_core::judgment::KeyRing;
use dlc_core::principal::Principal;
use dlc_core::syntax::Signature;
use portcullis_core::combinators::{CheckResult, PolicyCheck, PolicyRequest};

/// Cryptographic, proof-carrying admission: the caller must present an issuer-signed
/// capability for the requested tool. Backed by DLC-D's `admit_joint` (no false admits).
pub struct SaysAdmission {
    keyring: KeyRing,          // host-provisioned: the trusted issuer keys
    issuer:  Principal,        // the issuer this check requires
    sig:     Signature,        // the credential presented for this invocation
}

impl PolicyCheck for SaysAdmission {
    fn check(&self, req: &PolicyRequest) -> CheckResult {
        // req.operation IS the tool name; cap_atom binds it to the signed capability.
        match decide(&self.keyring, &self.issuer, &req.operation, &self.sig) {
            Decision::Admit    => CheckResult::Allow,
            Decision::Deny(r)  => CheckResult::Deny(r.to_string()),
        }
    }
    fn name(&self) -> &str { "dlc-d/says-admission" }
}
```

Composition (all on the nucleus side):

```rust
let admission = AllOf::new(vec![
    Box::new(ManifestAdmission::from(manifest)), // structural — portcullis's existing rules
    Box::new(SaysAdmission { keyring, issuer, sig }), // cryptographic + proof-carrying — DLC-D
]);
// Admit iff BOTH: the manifest is structurally sound AND the caller holds a valid issuer-signed cap.
```

Because `CheckResult::meet` is deny-dominant, adding `SaysAdmission` can only *narrow* what portcullis
admits — it never widens. It is a pure strengthening of the boundary.

## 4. Trust boundary (what DLC-D proves vs. what the host supplies)

| Concern | Who owns it | Guarantee |
|---|---|---|
| "Does this credential verify for this tool?" | **DLC-D** (`decide`) | real Ed25519; fail-closed; tool-bound via `cap_atom` |
| "Is a positive verdict backed by the model?" | **DLC-D** (`admit_joint`) | no false admits on `AdmitFrag` (machine-checked) |
| "Which issuer keys are trusted?" | **host** (the `KeyRing`) | host provenance decision — DLC-D does not choose keys |
| "What is the issuer's identity?" | **host** (the `Principal`) | host supplies; DLC-D checks the signature against it |
| "Which runtime tool name ↔ which `Cap<Invoke<T>>`?" | **host + macro** | `cap_atom` is the shared binding; the host must name tools consistently |
| "Does the tool *behave* as its manifest claims?" | **neither yet** | out of scope — portcullis's own named limitation; DLC-D adds authorization, not behavioral conformance |

## 5. The PR proposal (concrete)

Against the nucleus repo (pin the new rev in this workspace afterward, per `CLAUDE.md`):

1. **Dependency.** Add `dlc-d = { path/version = … }` to the `portcullis` (production) crate — **not** to
   `portcullis-core`, which must stay Aeneas-dependency-free. `SaysAdmission` lives in `portcullis`
   (which already imports serde/etc.), so the Aeneas fence on `portcullis-core` is untouched — symmetric
   to DLC-D's own fence (`dlc-crypto` is a `dlc-d` dep, never a `dlc-core` dep).
2. **The adapter.** Add `crates/portcullis/src/says_admission.rs` (the ~15-line `SaysAdmission` above)
   + a round-trip test mirroring `dlc_d::admission::tests` (valid cap admits; wrong-tool denies; unknown
   issuer denies).
3. **Wiring.** At the tool-call boundary where `check_admission` is invoked, compose `SaysAdmission` into
   the existing `AllOf` when a governed tool declares an issuer. The keyring is provisioned from the
   host's existing key-management (the same source portcullis already trusts for manifest signatures).
4. **No `portcullis-core` change.** The verified lattice core is not touched; this is an additive check
   at the composition layer.

## 6. Honest fences

- **`admit()` is not yet proved Lean-equivalent to the type-checker path** (`spec/joint-admission.md`
  #18 fence): `admit_joint` relates the *checker's* verdict to a `Deriv`; relating the *signed cap atom*
  to that `Deriv`'s cap prop is future metatheory. `SaysAdmission` composes the two guarantees at the
  entry point (typeability ∧ signature validity); it does not collapse them into one theorem.
- **Keyring provenance is the host's responsibility.** DLC-D proves a credential verifies against a
  keyring; it does not decide which keys belong in it. A misprovisioned keyring admits what its keys sign.
- **Behavioral conformance is out of scope** (portcullis's own limitation): admission authorizes the
  *invocation*; it does not prove the tool does only what its manifest declares.
- **Fragment scope.** The proof-carrying guarantee is over `AdmitFrag` (the current macro shape). Richer
  admission envelopes extend `AdmitFrag` and re-run the composition (`spec/joint-admission.md`).

## References (prior art, retrieved 2026-07-24)

- Before the Tool Call: Deterministic Pre-Action Authorization — arXiv 2603.20953 (the PEP-at-the-tool-boundary idiom).
- Sovereign Execution Broker: Certificate-Bound Authority in Agentic Control Planes — arXiv 2606.20520.
- Capability Gates Are Not Authorization: Confused-Deputy Failures in LLM Agent Frameworks — arXiv 2606.28679
  (why a structural capability gate ≠ authorization — the exact gap `SaysAdmission` fills).
- aiAuthZ: Off-Host, Identity-Bound Authorization for AI Agents — arXiv 2607.05518.
