# R6.1b — the replication wire protocol, and what the symbolic model obligates

*2026-07-24. Branch `dlc-d/phase0-carve`. Companion to `spec/r6-1-node-design.md`
(R6.1a, the in-process node) and to `models/tamarin/dlcd-replication.spthy` +
`models/tamarin/dlcd-replication-bite.spthy`.*

R6.1a shipped a running cluster over a **trusted in-process transport** and introduced
no wire encoding at all, because `CLAUDE.md` requires the Tamarin model before the wire.
This document is that model's output: the message shapes, the properties proved about
them, and the obligations the socket implementation inherits.

**Status:** models done and proved (Tamarin + ProVerif); the authenticated protocol layer
(`src/proto.rs`), the authenticated node (`src/auth.rs`, `AuthNode`), the wire codec
(`src/codec.rs`), and the async byte transport (`src/netauth.rs`) that runs a cluster over
tokio with every message crossing the channel as encoded bytes. **Remaining:** only the literal
socket carrier (bind/connect) — the channel in `netauth.rs` carries exactly the bytes a socket
would, so that is a carrier swap, not a protocol change. The authenticated networked node is
complete end-to-end over an in-process byte transport.

---

## 1. Why Tamarin, when Lean already proves agreement

Agreement, convergence, linearizability and liveness are machine-checked in Lean
(`DLCD.agreement`, `replicas_converge_via_consensus`, `single_linearization`,
`weakfair_terminates`) and transported to the deployed Rust core (`DLCD.Transport.rust_*`).
Tamarin re-proves none of that and could not: it is a Dolev-Yao protocol prover, not a
consensus-safety prover.

It answers the question Lean cannot, and which the node must answer before it speaks over
a network:

> `rust_capability_safety` is **conditioned** on `DLCD.Authorized` and `WellFormedLog`.
> Over a trusted channel those premises are free. Over a network they are not. What
> cryptographic structure must the wire have so an active attacker cannot make an honest
> replica apply a command whose premises fail?

So the model is a **design-obligation generator**. Each lemma is a requirement on the
implementation; the message shapes are what discharge them.

## 2. The messages

```
Issue_cap  I → *   ⟨'cmd', cmd, I, sign(⟨'cap', cmd⟩, skI)⟩
Propose    L → *   ⟨'propose', L, slot, cmd, I, capsig, sign(⟨'propose', slot, cmd⟩, skL)⟩
Vote       R → L   ⟨'vote', R, slot, cmd, sign(⟨'vote', slot, cmd⟩, skR)⟩
Commit     L → *   ⟨'commit', slot, cmd, ⟨'qc', R1, s1, R2, s2⟩, sign(⟨'commit', slot, cmd⟩, skL)⟩
```

`Commit` carries a **quorum certificate** — the two vote signatures themselves.

## 3. The one design decision that matters: `Apply` does not trust the leader

The applying replica verifies **the certificate**, not the sender. The commit's own
signature is bound by the rule and then deliberately ignored — and every lemma still
holds. That is the machine-checked content of "the leader is not trusted".

The weaker alternative — accept a leader-signed commit — would make agreement conditional
on the leader not equivocating, i.e. true only for a *crash-fault* leader. Certificate
checking makes agreement survive a **Byzantine** leader. Cost: commit messages carry two
signatures instead of none.

**Obligation:** if the socket implementation ever "optimizes" `Apply` into trusting the
commit signature, `slot_agreement` stops being a statement about the deployed protocol.

## 4. What is proved (all verified, Tamarin 1.12.0)

| Lemma | Statement | Steps |
|---|---|---|
| `applied_implies_quorum` | nothing is applied that two *distinct* replicas did not vote for | 19 |
| `applied_implies_capability` | an applied command's capability really was issued | 46 |
| `slot_agreement` | two replicas applying at the same slot apply the **same** command — even with an unauthenticated commit sender | 102 |
| `cap_check_binds_issuer` | an honest replica accepts a capability only if the **issuer it names** signed it — no escape via a compromised leader | 24 |
| `exec_apply` | a full honest run exists (anti-vacuity for the above) | 16 |
| `exec_cap_checked` | the capability-checking path is actually reached | 18 |

### 4.0 Which check carries the capability property — a correction

`applied_implies_capability` is enforced **redundantly**: both the leader (before
proposing) and every voter (before voting) verify the capability. Perturbation runs in the
ProVerif cross-check measured it: remove the voter's check → still provable; remove the
leader's → still provable; remove **both** → false.

So that lemma does not say which participant carries the property, and the first draft of
this document and of both models claimed the voter's check was what made it provable.
That was wrong. It matters because the design stance is that **the leader is not trusted**
— a capability property a compromised leader can void is not the property we want.

`cap_check_binds_issuer` is the repair: it binds the issuer in the *premise* (universally
quantified) and names *that issuer's* key in the escape clause, rather than "some key
somewhere". Deleting the voter's check falsifies it — Tamarin `falsified — found trace
(10 steps)`, ProVerif `is false` — which is what makes it, not `applied_implies_capability`,
the lemma the implementation must preserve.

Each all-traces lemma carries an explicit reveal escape clause, so it says exactly
"unless a long-term key leaked".

`applied_implies_capability` is the one that matters most to the program: it is how the
networked node will **discharge** the `Authorized` premise that Lean's capability-safety
currently assumes — carrying authorization end-to-end under an active attacker.

### 4.1 Anti-vacuity is not optional here

`dlc.spthy` carried a lemma that passed *vacuously* for months (`secrecy_ltk`, premise on a
persistent fact no rule emitted as an action) and Tamarin reported it `verified`. The
paired exists-trace lemma that would have caught it did not exist. Both all-traces groups
here are therefore paired with executability lemmas.

## 5. The bite, and why it is a separate theory

`dlcd-replication-bite.spthy` is the same theory with **exactly one thing removed**: the
`unique_slot_open` restriction (one vote per replica per slot). Its single lemma is an
*exists-trace* and CI requires it **verified** — a verified exists-trace means the attack
is reachable:

> two honest replicas apply **different** commands at the **same** slot, with **no key
> compromise anywhere** in the trace. Pure protocol failure, not a crypto failure.

Stating the bite as an exists-trace (rather than letting `slot_agreement` be falsified)
keeps the CI gate uniform: every lemma in every model must come back `verified`, so a
silently-deleted bite cannot pass as green.

### 5.1 The differential gate — because two green files prove nothing

Run separately, both theories report `verified` and CI is green. That is the shape of a
gate that checks nothing: if the guard were removed from the *main* model too, or the
models drifted apart, both would still pass. `scripts/check-tamarin-bite.sh` asserts the
differential itself:

- **(a)** the two theories have byte-identical **rules**; the *only* difference is the
  removed restriction (perturb the information, never the shape);
- **(b)** the bite's attack lemma, transplanted verbatim into the **guarded** model, is
  `falsified — no trace found` there.

Measured: `verified (28 steps)` in the bite, `falsified — no trace found (102 steps)` in
the guarded model, 8 identical rules. The gate was itself perturbation-tested: deleting
`unique_slot_open` from the main model makes it fail, and fail naming that cause.

## 6. Obligations on the R6.1b implementation

1. **`Apply` verifies the quorum certificate**, not the commit's sender (§3).
2. **Every voter verifies the capability signature** before voting — not merely the
   leader. This is what R6.1a does *not* do (its disclosed fence: `cap` is carried, not
   checked). Voter-side checking is what `cap_check_binds_issuer` needs; leader-side
   checking alone would leave the property voidable by a compromised leader, which the
   design explicitly refuses to trust (§4.0).
3. **One vote per (replica, slot)**, enforced structurally. The node's `slot ==
   next_slot()` guard is the current realization; whatever replaces it must be equally
   unforgeable locally (§5).
4. **Distinct voters in a certificate** — a certificate of one replica's two signatures is
   not a quorum.
5. Payload encoding reuses `dlc_protocol::wire` verbatim; this protocol adds a framing
   layer, not a second term encoding.

### 6.1 What `proto.rs` implements (done)

`crates/dlc-d-node/src/proto.rs` is the authenticated layer, each function mapped to a
model premise:

- `verify_commit` takes **no sender argument** — it checks the certificate, the Byzantine-
  leader-tolerant `slot_agreement` obligation (§3).
- `verify_proposal` checks the capability before a vote — `cap_check_binds_issuer` (§4.0).
- `verify_qc` counts **distinct signers**, not signatures. This is the [Nethermind XDC
  duplicate-signature quorum bypass](https://github.com/NethermindEth/nethermind/issues/11026):
  counting raw votes lets one validator satisfy quorum alone with several valid signatures
  over the same message (Ed25519 determinism is *not* a defence — a key-holder can produce
  many valid byte-different signatures). It is the code image of the model's `Neq($R1,$R2)`.
- Domain-separated signing prefixes (`cap`/`propose`/`vote`) so a signature can't be
  repurposed across message kinds — the byte-level image of the models' tag-in-signed-tuple.
- `Roster::new` rejects duplicate members (one key, two seats).

Negative tests pin each: single-signer forgery rejected, non-member votes ignored, cross-slot
and cross-command certificate replay rejected, mismatched capability rejected at the proposal.
`tests/authenticated.rs` composes the whole chain and shows the certified command is exactly
what the verified `commit`/`world_step` then applies — so `proto` is reachable from the
verified core, not just from its own tests.

## 6.2 The authenticated node (`src/auth.rs`, `AuthNode`) — two proof chains, both live

Where `proto` and the verified core meet on a running decision path. The design decision that
matters: there are two independently-verified decision surfaces, and the node keeps **both**
rather than substituting one for the other.

- `dlc_d_rsm::consensus::decided` — the strict-majority tally, transported to Lean as
  `rust_consensus_agreement` — makes the leader's **decision**.
- `proto::{verify_proposal, verify_vote, verify_commit}` — Tamarin/ProVerif-proved — gate
  **admissibility**: what may reach the decision, and what a follower may apply.

Authentication decides admissibility; the verified predicate decides agreement. A forged vote
never reaches `decided`; a forged commit never reaches `commit`/`world_step`. Neither proof is
weakened for the other. A replica is its Ed25519 key; its `u32` ballot index is its roster
position, so the ballot stays the exact shape `rust_consensus_agreement` reasons about —
authentication maps a verified signer to that index, it does not change the index space.

Model-state discipline is preserved: `AuthNode`'s entire state is a singleton `GlobalConfig`
replaced only by `commit`/`world_step`, and `purity.rs` scans `auth.rs` too (the transition
count it pins went 2 → 4, one pair per node type).

Tests (deterministic in-memory harness, no async): a 3-node authenticated cluster converges on
the changed store; one crash within budget still commits; a non-member vote never enters the
ballot; a single-signer (XDC-style) certificate is rejected by a follower; a vote for the wrong
command does not count; a seed that does not match its roster seat is refused at construction.

## 6.3 The wire codec + async transport (`src/codec.rs`, `src/netauth.rs`)

`AuthMsg` crosses the wire as a CBOR `[tag, body]` frame. The codec hand-rolls
`ciborium::Value` (the repo idiom — no serde-derive on terms) and encodes the embedded terms
through `dlc_protocol::wire::encode` **verbatim**. That verbatim reuse is not cosmetic: a
`proto` signature is computed over `wire::canonical_bytes(&payload)`, so if decode did not
reproduce the payload byte-for-byte the decoded message's signatures would stop verifying.

So the codec's load-bearing test is **not** `encode∘decode = id` — it is *the decoded message
still verifies* (`roundtrip_preserves_verification`: sign → encode → decode → verify = true for
proposal, vote, commit). Plus: malformed frames are clean errors not panics, and an exhaustive
single-byte-flip test (`corruption_never_passes_verification`) confirms no corruption ever
decodes into a *different* verifying message.

`netauth.rs` runs `AuthNode` over tokio, each peer exchanging `Vec<u8>` frames and decoding at
the wire boundary (a frame that fails to decode is dropped, as a real node drops a bad packet).
This is what makes the codec load-bearing rather than a self-tested library. Its integration
tests (`tests/networked.rs`) run the whole stack — `proto` auth + Lean-transported `decided` +
codec + tokio — to convergence, plus crash-within-budget and the over-budget stall, all over
the byte transport. The channel carries exactly the bytes a socket would, so the only remaining
piece is the literal bind/connect carrier — a swap, not a protocol change.

## 7. Fences — what this model does not say

- **Fixed roster of 3, quorum 2.** Bounding participants is standard for quorum models in
  Tamarin and is *required* here: quorum intersection is what makes `slot_agreement` true,
  and unbounded replica sets admit disjoint 2-quorums. Lean carries the general statement
  (`quorum_intersect` over `Finset (Fin n)`); Tamarin carries the wire structure at n=3.
  Neither subsumes the other.
- **No liveness.** A Dolev-Yao adversary may drop every message, so no progress property
  can hold. Liveness is Lean's, under `WeakFair`, with the failure budget as contract; the
  runtime shadow is the over-budget stall in `crates/dlc-d-node/tests/cluster.rs`.
- **No multi-slot log reasoning.** `slot_agreement` is per-slot. Cross-slot log matching is
  Lean's `log_agreement` / `log_agreement_eq`.
- **ProVerif cross-check not yet written.** `CLAUDE.md` wants Tamarin then ProVerif before
  the wire; the ProVerif companion (`models/proverif/dlcd-replication.pv`) is the next
  step and the wire must wait for it.
- **Static key compromise only.** Adaptive corruption is out of scope, as in `dlc.spthy`.

## 8. Finding recorded while building this: `dlc.spthy` may be unsound — NOW FIXED

**Update, same day:** the fix landed. `dlc.spthy`'s two verifying rules were converted to
the `verify(...)` idiom, all 7 lemmas re-proved (identical step counts, so the properties
genuinely held — the caveat was on the *analysis*, not on the protocol), and its CI
wellformedness gate is now strict. Both checks were perturbation-tested: deleting the
says-half verification falsifies `non_splicing` (6 steps), deleting the evidence
verification falsifies `no_silent_discharge` (9 steps). The original finding is kept below
because the failure mode — a tool-reported soundness caveat riding under a gate that greps
only for `falsified|incomplete` — is the reusable lesson.

### 8.1 The finding as originally recorded

Under Tamarin 1.12.0 the pre-existing delegation model reports:

```
WARNING: 1 wellformedness check failed!
         The analysis results might be wrong!
Rule Delegate_Accept: Failed to derive Variable(s): skP, skQ
Rule Discharge_Accept: Failed to derive Variable(s): skP, skQ
```

Its 7 lemmas still verify, but Tamarin itself flags the results as possibly wrong: the
model checks signatures by pattern-matching `sign(msg, skP)` against `!Pk(P, pk(skP))`,
which the message-derivation check cannot justify. The CI gate greps for
`falsified|incomplete` and so never failed on it — the same class of silent gap this file's
own history records.

The replication models avoid it by using the derivation-clean `verify(sig, msg, pk) = true`
idiom, and their CI step asserts zero warnings positively. Fixing `dlc.spthy` meant
re-proving all 7 of its lemmas under the new idiom — done, see §8 above.

Worth stating plainly, since the alternative was tempting: Tamarin's manual offers
`[no_derivcheck]` to suppress the check on a rule the author believes is fine. That would
have turned a *known* caveat into an *unknown* one — the warning disappears, the modelling
gap does not. The idiom change was taken instead, which also makes the adversary strictly
stronger (semantic verification admits any term the equational theory reduces, rather than
only syntactic `sign(...)` shapes). That the lemmas survived that strengthening is the
result; had one failed, the failure would have been the real finding.
