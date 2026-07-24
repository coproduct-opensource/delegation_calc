//! The authenticated replication protocol — the checks the symbolic models
//! demand, implemented.
//!
//! Model: `models/tamarin/dlcd-replication.spthy` (+ the ProVerif cross-check at
//! `models/proverif/dlcd-replication.pv`). Spec: `spec/r6-1b-replication-protocol.md`.
//! Every verification function here corresponds to a rule premise in that model,
//! and the correspondence is the point: the model's lemmas are statements about
//! these checks, so weakening one here silently invalidates a proof over there.
//!
//! # What the models obligate, and where each obligation lives
//!
//! | Model requirement | Here |
//! |---|---|
//! | `Apply` verifies the quorum certificate, NOT the commit's sender | [`verify_commit`] takes no sender argument at all |
//! | every voter verifies the capability (`cap_check_binds_issuer`) | [`verify_proposal`] — called before voting |
//! | a certificate needs two DISTINCT voters (`Neq($R1,$R2)`) | [`verify_qc`] counts DISTINCT signers |
//! | signatures bind the slot (no cross-slot replay) | the signing domains below |
//!
//! # Domain separation
//!
//! Each signature covers a distinct constant prefix, so a signature made for one
//! purpose cannot be replayed as another. The symbolic models get this for free
//! from their `'cap'` / `'propose'` / `'vote'` tags inside the signed tuple;
//! byte-level protocols have to do it explicitly, and forgetting to is a classic
//! way to make a proved protocol unsound in implementation.
//!
//! # Term encoding
//!
//! Payloads are encoded with `dlc_protocol::wire::canonical_bytes` — the SAME
//! encoder `says`-credentials are signed under, not a second "canonical form" to
//! drift from it. This crate introduces no term encoding of its own.

use dlc_core::rsm::Command;
use dlc_crypto::ed25519;
use dlc_protocol::wire;

/// An Ed25519 public key — a replica's identity on the wire.
pub type PubKey = [u8; 32];

/// An Ed25519 signature.
pub type Sig = [u8; 64];

/// Domain-separation prefixes. Distinct by construction, checked by
/// `domains_are_distinct` in the test module.
const DOM_CAP: &[u8] = b"dlc-d/cap/v1";
const DOM_PROPOSE: &[u8] = b"dlc-d/propose/v1";
const DOM_VOTE: &[u8] = b"dlc-d/vote/v1";

/// The canonical bytes of a command: its payload under the protocol's existing
/// term encoder, plus its capability slot.
///
/// `cap` is included so a signature cannot be transplanted from a command
/// carrying one capability onto the same payload carrying another.
fn cmd_bytes(c: &Command) -> Vec<u8> {
    let mut v = wire::canonical_bytes(&c.payload);
    match &c.cap {
        Some(p) => {
            v.push(1);
            v.extend_from_slice(&wire::encode_prop(p));
        }
        None => v.push(0),
    }
    v
}

fn cap_msg(c: &Command) -> Vec<u8> {
    let mut m = DOM_CAP.to_vec();
    m.extend_from_slice(&cmd_bytes(c));
    m
}

fn propose_msg(slot: u32, c: &Command) -> Vec<u8> {
    let mut m = DOM_PROPOSE.to_vec();
    m.extend_from_slice(&slot.to_le_bytes());
    m.extend_from_slice(&cmd_bytes(c));
    m
}

fn vote_msg(slot: u32, c: &Command) -> Vec<u8> {
    let mut m = DOM_VOTE.to_vec();
    m.extend_from_slice(&slot.to_le_bytes());
    m.extend_from_slice(&cmd_bytes(c));
    m
}

/// The committee. Membership is pinned: a signature from a key outside the
/// roster is worth nothing, which is the implementation of the models' `roster`
/// restriction and their `!Pk` / `honest_keys` pinning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Roster {
    members: Vec<PubKey>,
}

impl Roster {
    /// Build a roster. Duplicate members are rejected — a roster listing the
    /// same key twice would inflate the quorum threshold's denominator while
    /// letting one signer count twice.
    pub fn new(members: Vec<PubKey>) -> Option<Roster> {
        for i in 0..members.len() {
            for j in (i + 1)..members.len() {
                if members[i] == members[j] {
                    return None;
                }
            }
        }
        Some(Roster { members })
    }

    /// Number of replicas.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// Whether the roster is empty.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// Is this key a committee member?
    pub fn contains(&self, k: &PubKey) -> bool {
        self.members.iter().any(|m| m == k)
    }

    /// Strict-majority test — the byte-level image of
    /// `dlc_d_rsm::consensus::is_quorum` (`2 * card > n`), which is what the
    /// transported `rust_consensus_agreement` reasons about.
    pub fn is_quorum(&self, distinct_signers: usize) -> bool {
        2 * distinct_signers > self.members.len()
    }
}

/// A capability credential: the issuer's signature over the command.
///
/// The wire form of the `says`-credential that `commit-I` demands as a subterm
/// and that `DLCD.Authorized` quantifies over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capability {
    /// The issuing principal.
    pub issuer: PubKey,
    /// Signature over `DOM_CAP || cmd_bytes`.
    pub sig: Sig,
}

/// A leader's proposal of a command for a slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proposal {
    /// The proposing leader.
    pub leader: PubKey,
    /// The slot being decided.
    pub slot: u32,
    /// The proposed command.
    pub cmd: Command,
    /// The command's capability credential.
    pub cap: Capability,
    /// Signature over `DOM_PROPOSE || slot || cmd_bytes`.
    pub sig: Sig,
}

/// A replica's vote for a command at a slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vote {
    /// The voting replica.
    pub voter: PubKey,
    /// The slot voted on.
    pub slot: u32,
    /// Signature over `DOM_VOTE || slot || cmd_bytes`.
    pub sig: Sig,
}

/// A quorum certificate: the votes themselves, so any receiver can check it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumCert {
    /// The votes backing the decision.
    pub votes: Vec<Vote>,
}

/// A commit: the decided command plus the certificate proving it was decided.
///
/// Note what this struct does NOT have: a sender field, or a sender's
/// signature. That absence is the design — see [`verify_commit`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commit {
    /// The decided slot.
    pub slot: u32,
    /// The decided command.
    pub cmd: Command,
    /// The certificate.
    pub qc: QuorumCert,
}

/// Sign a capability for a command.
pub fn issue_capability(seed: &[u8; 32], cmd: &Command) -> Capability {
    Capability {
        issuer: ed25519::public_key(seed),
        sig: ed25519::sign(seed, &cap_msg(cmd)),
    }
}

/// Verify a capability credential against the command it accompanies.
pub fn verify_capability(cap: &Capability, cmd: &Command) -> bool {
    ed25519::verify(&cap.issuer, &cap_msg(cmd), &cap.sig).is_ok()
}

/// Build a proposal.
pub fn propose(seed: &[u8; 32], slot: u32, cmd: Command, cap: Capability) -> Proposal {
    let sig = ed25519::sign(seed, &propose_msg(slot, &cmd));
    Proposal {
        leader: ed25519::public_key(seed),
        slot,
        cmd,
        cap,
        sig,
    }
}

/// Verify a proposal before voting on it: the leader is a committee member, its
/// signature is good, AND the capability verifies.
///
/// The capability check here is the load-bearing one. `cap_check_binds_issuer`
/// (both models) says an honest replica accepts a capability only if the issuer
/// it names really signed it, with NO escape via a compromised leader — and it
/// is falsified precisely by deleting this check. Leader-side checking alone is
/// not enough, because the leader is not trusted.
pub fn verify_proposal(p: &Proposal, roster: &Roster) -> bool {
    if !roster.contains(&p.leader) {
        return false;
    }
    if ed25519::verify(&p.leader, &propose_msg(p.slot, &p.cmd), &p.sig).is_err() {
        return false;
    }
    verify_capability(&p.cap, &p.cmd)
}

/// Cast a vote for a proposal's command at its slot.
pub fn vote(seed: &[u8; 32], slot: u32, cmd: &Command) -> Vote {
    Vote {
        voter: ed25519::public_key(seed),
        slot,
        sig: ed25519::sign(seed, &vote_msg(slot, cmd)),
    }
}

/// Verify a single vote binds this exact (slot, command) and comes from the
/// committee.
pub fn verify_vote(v: &Vote, slot: u32, cmd: &Command, roster: &Roster) -> bool {
    v.slot == slot
        && roster.contains(&v.voter)
        && ed25519::verify(&v.voter, &vote_msg(slot, cmd), &v.sig).is_ok()
}

/// Verify a quorum certificate for `(slot, cmd)`: enough **distinct** committee
/// members validly signed a vote for it.
///
/// # Counting distinct SIGNERS, not signatures
///
/// This is the one place where a natural implementation is a critical bug.
/// Nethermind's XDC consensus counted raw vote objects, so one validator could
/// submit several distinct signatures over the same vote and satisfy quorum
/// alone — forged certificates, premature finality, HotStuff safety broken with
/// fewer than the required validators
/// (<https://github.com/NethermindEth/nethermind/issues/11026>).
///
/// Ed25519 signing is deterministic, so *identical* duplicates would collapse on
/// their own; that is not a defence. A signer holding its own key can produce
/// many valid, byte-DIFFERENT signatures over the same message. Deduplication
/// must therefore key on the SIGNER, which is what this does.
///
/// The symbolic model has the same requirement as `Neq($R1, $R2)` on the `Apply`
/// rule, and `applied_implies_quorum` is a statement about two *distinct*
/// voters. So this is not defensive coding — it is what makes the proof apply to
/// this code.
pub fn verify_qc(qc: &QuorumCert, slot: u32, cmd: &Command, roster: &Roster) -> bool {
    let mut signers: Vec<PubKey> = Vec::new();
    for v in &qc.votes {
        if !verify_vote(v, slot, cmd, roster) {
            return false;
        }
        if !signers.contains(&v.voter) {
            signers.push(v.voter);
        }
    }
    roster.is_quorum(signers.len())
}

/// Verify a commit — by checking its CERTIFICATE, with no reference to who sent
/// it.
///
/// There is deliberately no `sender` parameter and no sender signature in
/// [`Commit`]. The models prove `slot_agreement` while `Apply` never
/// authenticates the commit's sender, which is what makes agreement survive a
/// **Byzantine leader**: anyone, including the adversary, may relay a
/// certificate, and it is worthless unless the votes inside it check out.
///
/// If a future change adds sender authentication and starts relying on it, the
/// proof stops describing this code.
pub fn verify_commit(c: &Commit, roster: &Roster) -> bool {
    verify_qc(&c.qc, c.slot, &c.cmd, roster)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dlc_core::syntax::{Prop, Term};

    fn seed(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn cmd(tag: u32) -> Command {
        Command {
            payload: Term::Lam(
                Box::new(Prop::Atom(tag)),
                Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
            ),
            cap: None,
        }
    }

    fn roster3() -> Roster {
        Roster::new(vec![
            ed25519::public_key(&seed(1)),
            ed25519::public_key(&seed(2)),
            ed25519::public_key(&seed(3)),
        ])
        .expect("distinct members")
    }

    /// A full honest run verifies — without this, every negative test below
    /// could pass by the verifier rejecting everything.
    #[test]
    fn honest_run_verifies() {
        let r = roster3();
        let c = cmd(0);
        let cap = issue_capability(&seed(9), &c);
        let p = propose(&seed(1), 7, c.clone(), cap);
        assert!(verify_proposal(&p, &r));

        let qc = QuorumCert {
            votes: vec![vote(&seed(1), 7, &c), vote(&seed(2), 7, &c)],
        };
        assert!(verify_qc(&qc, 7, &c, &r));
        assert!(verify_commit(
            &Commit {
                slot: 7,
                cmd: c,
                qc
            },
            &r
        ));
    }

    /// THE XDC BUG (<https://github.com/NethermindEth/nethermind/issues/11026>):
    /// one replica must not be able to satisfy a quorum by itself, however many
    /// valid signatures it contributes.
    #[test]
    fn one_replica_cannot_forge_a_quorum() {
        let r = roster3();
        let c = cmd(0);
        let v = vote(&seed(1), 7, &c);
        // Same signer, repeated. Every vote here is individually VALID.
        let qc = QuorumCert {
            votes: vec![v.clone(), v.clone(), v],
        };
        for x in &qc.votes {
            assert!(verify_vote(x, 7, &c, &r), "each vote is valid on its own");
        }
        assert!(
            !verify_qc(&qc, 7, &c, &r),
            "three valid signatures from ONE signer are not a quorum of three"
        );
    }

    /// A vote from outside the committee doesn't count, even though the
    /// signature itself is perfectly valid.
    #[test]
    fn non_member_votes_do_not_count() {
        let r = roster3();
        let c = cmd(0);
        let outsider = vote(&seed(42), 7, &c);
        assert!(!verify_vote(&outsider, 7, &c, &r));
        let qc = QuorumCert {
            votes: vec![vote(&seed(1), 7, &c), outsider],
        };
        assert!(!verify_qc(&qc, 7, &c, &r));
    }

    /// Votes bind their slot: a certificate collected for slot 7 cannot be
    /// replayed to decide slot 8.
    #[test]
    fn certificates_do_not_replay_across_slots() {
        let r = roster3();
        let c = cmd(0);
        let qc = QuorumCert {
            votes: vec![vote(&seed(1), 7, &c), vote(&seed(2), 7, &c)],
        };
        assert!(verify_qc(&qc, 7, &c, &r));
        assert!(!verify_qc(&qc, 8, &c, &r));
    }

    /// Votes bind their command: a certificate for one command cannot decide
    /// another at the same slot.
    #[test]
    fn certificates_do_not_transfer_across_commands() {
        let r = roster3();
        let (c1, c2) = (cmd(0), cmd(1));
        let qc = QuorumCert {
            votes: vec![vote(&seed(1), 7, &c1), vote(&seed(2), 7, &c1)],
        };
        assert!(verify_qc(&qc, 7, &c1, &r));
        assert!(!verify_qc(&qc, 7, &c2, &r));
    }

    /// `cap_check_binds_issuer`, in code: a command whose capability was signed
    /// over a DIFFERENT command is rejected, so a leader cannot staple a valid
    /// credential onto an unauthorized command.
    #[test]
    fn capability_binds_to_its_command() {
        let r = roster3();
        let (c1, c2) = (cmd(0), cmd(1));
        let cap_for_c1 = issue_capability(&seed(9), &c1);
        assert!(verify_capability(&cap_for_c1, &c1));
        assert!(!verify_capability(&cap_for_c1, &c2));

        // Stapled onto c2 and proposed: the proposal must not verify.
        let p = propose(&seed(1), 7, c2, cap_for_c1);
        assert!(!verify_proposal(&p, &r));
    }

    /// A proposal from a non-member is rejected even with a good capability.
    #[test]
    fn proposals_from_outside_the_committee_are_rejected() {
        let r = roster3();
        let c = cmd(0);
        let cap = issue_capability(&seed(9), &c);
        let p = propose(&seed(42), 7, c, cap);
        assert!(!verify_proposal(&p, &r));
    }

    /// Domain separation: a capability signature is not a valid vote signature
    /// and vice versa, so signatures cannot be repurposed across message kinds.
    #[test]
    fn domains_are_distinct() {
        let c = cmd(0);
        assert_ne!(cap_msg(&c), vote_msg(0, &c));
        assert_ne!(propose_msg(0, &c), vote_msg(0, &c));

        // A capability signature transplanted into a Vote must not verify.
        let cap = issue_capability(&seed(1), &c);
        let forged = Vote {
            voter: ed25519::public_key(&seed(1)),
            slot: 0,
            sig: cap.sig,
        };
        assert!(!verify_vote(&forged, 0, &c, &roster3()));
    }

    /// A roster with a duplicate member is refused at construction — otherwise
    /// one key could occupy two committee seats.
    #[test]
    fn duplicate_roster_members_are_refused() {
        let k = ed25519::public_key(&seed(1));
        assert!(Roster::new(vec![k, k]).is_none());
        assert!(Roster::new(vec![k, ed25519::public_key(&seed(2))]).is_some());
    }

    /// The quorum threshold matches `dlc_d_rsm::consensus::is_quorum`.
    #[test]
    fn quorum_threshold_matches_the_verified_predicate() {
        let r = roster3();
        for card in 0..=3usize {
            assert_eq!(
                r.is_quorum(card),
                dlc_d_rsm::consensus::is_quorum(card as u32, r.len() as u32),
                "threshold disagrees with the verified predicate at card={card}"
            );
        }
    }
}
