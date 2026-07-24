# R6.1b — the replication wire protocol, and what the symbolic model obligates

*2026-07-24. Branch `dlc-d/phase0-carve`. Companion to `spec/r6-1-node-design.md`
(R6.1a, the in-process node) and to `models/tamarin/dlcd-replication.spthy` +
`models/tamarin/dlcd-replication-bite.spthy`.*

R6.1a shipped a running cluster over a **trusted in-process transport** and introduced
no wire encoding at all, because `CLAUDE.md` requires the Tamarin model before the wire.
This document is that model's output: the message shapes, the properties proved about
them, and the obligations the socket implementation inherits.

**Status: model done and proved; wire NOT implemented.** Nothing in `crates/` speaks
this protocol yet.

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
| `applied_implies_capability` | an applied command's capability really was issued by the principal named in it | 46 |
| `slot_agreement` | two replicas applying at the same slot apply the **same** command — even with an unauthenticated commit sender | 102 |
| `exec_apply` | a full honest run exists (anti-vacuity for the three above) | 16 |
| `exec_cap_checked` | the capability-checking path is actually reached | 18 |

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
2. **Every voter verifies the capability signature** before voting. This is what R6.1a
   does *not* do — its disclosed fence is that `cap` is carried, not checked. The
   networked node must check it, or `applied_implies_capability` says nothing about it.
3. **One vote per (replica, slot)**, enforced structurally. The node's `slot ==
   next_slot()` guard is the current realization; whatever replaces it must be equally
   unforgeable locally (§5).
4. **Distinct voters in a certificate** — a certificate of one replica's two signatures is
   not a quorum.
5. Payload encoding reuses `dlc_protocol::wire` verbatim; this protocol adds a framing
   layer, not a second term encoding.

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

## 8. Finding recorded while building this: `dlc.spthy` may be unsound

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
idiom, and their CI step asserts zero warnings positively. **Fixing `dlc.spthy` means
re-proving all 7 of its lemmas under the new idiom and is tracked as the next increment**
(roadmap §6b) — it is a caveat on existing claims, not on anything introduced here.
