//! The wire codec for [`crate::auth::AuthMsg`] — the byte carrier for the
//! authenticated replication protocol.
//!
//! Design: `spec/r6-1b-replication-protocol.md` §6.3. This is the piece
//! `CLAUDE.md`'s "reuse `dlc_protocol::wire` verbatim, add a framing layer not a
//! second term encoding" obligation lands on.
//!
//! # The one property that must hold, and the test that pins it
//!
//! A signature in `proto` is computed over `cmd_bytes`, which is built from
//! `dlc_protocol::wire::canonical_bytes(&payload)`. So decoding MUST reproduce
//! the payload term byte-for-byte, or the decoded message's signatures stop
//! verifying. That is not a nice-to-have: a codec that round-trips the *struct*
//! but perturbs the term encoding would silently break authentication on the
//! wire while every struct-equality test passed. The load-bearing test here is
//! therefore not `encode∘decode = id` — it is **the decoded message still
//! verifies** (sign → encode → decode → verify = true), exercised in
//! `roundtrip_preserves_verification`.
//!
//! # Idiom
//!
//! Hand-rolled `ciborium::Value`, matching `dlc_protocol::wire` (the repo does
//! not derive `serde` on terms). Terms and props go through `wire::encode` /
//! `wire::encode_prop` verbatim; keys and signatures are fixed-size `Bytes`;
//! slots are integers. Deterministic: the same message encodes to the same
//! bytes, because every sub-encoder is deterministic.

use ciborium::Value;

use dlc_core::rsm::Command;
use dlc_core::syntax::Prop;
use dlc_protocol::wire;

use crate::auth::AuthMsg;
use crate::proto::{Capability, Commit, Proposal, QuorumCert, Vote};

/// A codec error — malformed frame, or a field that does not decode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodecError(pub String);

impl core::fmt::Display for CodecError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "authmsg codec error: {}", self.0)
    }
}

impl std::error::Error for CodecError {}

fn err<T>(msg: &str) -> Result<T, CodecError> {
    Err(CodecError(msg.to_string()))
}

// ---------------------------------------------------------------------------
// value helpers
// ---------------------------------------------------------------------------

fn as_array(v: &Value, ctx: &str) -> Result<Vec<Value>, CodecError> {
    v.as_array()
        .cloned()
        .ok_or_else(|| CodecError(format!("{ctx}: expected array")))
}

fn as_bytes(v: &Value, ctx: &str) -> Result<Vec<u8>, CodecError> {
    v.as_bytes()
        .cloned()
        .ok_or_else(|| CodecError(format!("{ctx}: expected bytes")))
}

fn as_u32(v: &Value, ctx: &str) -> Result<u32, CodecError> {
    let i = v
        .as_integer()
        .ok_or_else(|| CodecError(format!("{ctx}: expected integer")))?;
    u128::try_from(i)
        .ok()
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| CodecError(format!("{ctx}: integer out of u32 range")))
}

fn fixed<const N: usize>(bytes: Vec<u8>, ctx: &str) -> Result<[u8; N], CodecError> {
    <[u8; N]>::try_from(bytes.as_slice())
        .map_err(|_| CodecError(format!("{ctx}: expected {N} bytes, got {}", bytes.len())))
}

// ---------------------------------------------------------------------------
// Command  (payload term + optional capability prop)
// ---------------------------------------------------------------------------

fn enc_command(c: &Command) -> Value {
    let cap = match &c.cap {
        Some(p) => Value::Bytes(wire::encode_prop(p)),
        None => Value::Null,
    };
    Value::Array(vec![Value::Bytes(wire::encode(&c.payload)), cap])
}

fn dec_command(v: &Value) -> Result<Command, CodecError> {
    let a = as_array(v, "command")?;
    if a.len() != 2 {
        return err("command: expected [payload, cap]");
    }
    let payload = wire::decode(&as_bytes(&a[0], "command.payload")?)
        .map_err(|e| CodecError(format!("{e}")))?;
    let cap: Option<Prop> = match &a[1] {
        Value::Null => None,
        other => Some(
            wire::decode_prop(&as_bytes(other, "command.cap")?)
                .map_err(|e| CodecError(format!("{e}")))?,
        ),
    };
    Ok(Command { payload, cap })
}

// ---------------------------------------------------------------------------
// proto structs
// ---------------------------------------------------------------------------

fn enc_cap(c: &Capability) -> Value {
    Value::Array(vec![
        Value::Bytes(c.issuer.to_vec()),
        Value::Bytes(c.sig.to_vec()),
    ])
}

fn dec_cap(v: &Value) -> Result<Capability, CodecError> {
    let a = as_array(v, "capability")?;
    if a.len() != 2 {
        return err("capability: expected [issuer, sig]");
    }
    Ok(Capability {
        issuer: fixed::<32>(as_bytes(&a[0], "capability.issuer")?, "capability.issuer")?,
        sig: fixed::<64>(as_bytes(&a[1], "capability.sig")?, "capability.sig")?,
    })
}

fn enc_proposal(p: &Proposal) -> Value {
    Value::Array(vec![
        Value::Bytes(p.leader.to_vec()),
        Value::Integer(p.slot.into()),
        enc_command(&p.cmd),
        enc_cap(&p.cap),
        Value::Bytes(p.sig.to_vec()),
    ])
}

fn dec_proposal(v: &Value) -> Result<Proposal, CodecError> {
    let a = as_array(v, "proposal")?;
    if a.len() != 5 {
        return err("proposal: expected [leader, slot, cmd, cap, sig]");
    }
    Ok(Proposal {
        leader: fixed::<32>(as_bytes(&a[0], "proposal.leader")?, "proposal.leader")?,
        slot: as_u32(&a[1], "proposal.slot")?,
        cmd: dec_command(&a[2])?,
        cap: dec_cap(&a[3])?,
        sig: fixed::<64>(as_bytes(&a[4], "proposal.sig")?, "proposal.sig")?,
    })
}

fn enc_vote(v: &Vote) -> Value {
    Value::Array(vec![
        Value::Bytes(v.voter.to_vec()),
        Value::Integer(v.slot.into()),
        Value::Bytes(v.sig.to_vec()),
    ])
}

fn dec_vote(v: &Value) -> Result<Vote, CodecError> {
    let a = as_array(v, "vote")?;
    if a.len() != 3 {
        return err("vote: expected [voter, slot, sig]");
    }
    Ok(Vote {
        voter: fixed::<32>(as_bytes(&a[0], "vote.voter")?, "vote.voter")?,
        slot: as_u32(&a[1], "vote.slot")?,
        sig: fixed::<64>(as_bytes(&a[2], "vote.sig")?, "vote.sig")?,
    })
}

fn enc_commit(c: &Commit) -> Value {
    let votes: Vec<Value> = c.qc.votes.iter().map(enc_vote).collect();
    Value::Array(vec![
        Value::Integer(c.slot.into()),
        enc_command(&c.cmd),
        Value::Array(votes),
    ])
}

fn dec_commit(v: &Value) -> Result<Commit, CodecError> {
    let a = as_array(v, "commit")?;
    if a.len() != 3 {
        return err("commit: expected [slot, cmd, votes]");
    }
    let votes = as_array(&a[2], "commit.votes")?
        .iter()
        .map(dec_vote)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Commit {
        slot: as_u32(&a[0], "commit.slot")?,
        cmd: dec_command(&a[1])?,
        qc: QuorumCert { votes },
    })
}

// ---------------------------------------------------------------------------
// AuthMsg  (tagged union)
// ---------------------------------------------------------------------------

/// Encode an [`AuthMsg`] to its wire bytes: a CBOR `[tag, body]` frame, the term
/// content going through `dlc_protocol::wire` verbatim.
pub fn encode_msg(m: &AuthMsg) -> Vec<u8> {
    let tagged = match m {
        AuthMsg::Propose(p) => Value::Array(vec![Value::Integer(0.into()), enc_proposal(p)]),
        AuthMsg::Vote(v) => Value::Array(vec![Value::Integer(1.into()), enc_vote(v)]),
        AuthMsg::Commit(c) => Value::Array(vec![Value::Integer(2.into()), enc_commit(c)]),
    };
    let mut buf = Vec::new();
    ciborium::into_writer(&tagged, &mut buf).expect("encoding to Vec cannot fail");
    buf
}

/// Decode an [`AuthMsg`] from a wire frame produced by [`encode_msg`].
pub fn decode_msg(bytes: &[u8]) -> Result<AuthMsg, CodecError> {
    let v: Value = ciborium::from_reader(bytes).map_err(|e| CodecError(format!("{e}")))?;
    let a = as_array(&v, "authmsg")?;
    if a.len() != 2 {
        return err("authmsg: expected [tag, body]");
    }
    match as_u32(&a[0], "authmsg.tag")? {
        0 => Ok(AuthMsg::Propose(dec_proposal(&a[1])?)),
        1 => Ok(AuthMsg::Vote(dec_vote(&a[1])?)),
        2 => Ok(AuthMsg::Commit(dec_commit(&a[1])?)),
        t => err(&format!("authmsg: unknown tag {t}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proto::{
        issue_capability, propose, verify_commit, verify_proposal, verify_vote, vote, Roster,
    };
    use dlc_core::syntax::Term;
    use dlc_crypto::ed25519;

    fn seed(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn cmd() -> Command {
        Command {
            payload: Term::Lam(
                Box::new(Prop::Atom(0)),
                Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
            ),
            cap: Some(Prop::Atom(7)),
        }
    }

    fn roster3() -> Roster {
        Roster::new(vec![
            ed25519::public_key(&seed(1)),
            ed25519::public_key(&seed(2)),
            ed25519::public_key(&seed(3)),
        ])
        .unwrap()
    }

    /// Structural round-trip for each variant.
    #[test]
    fn roundtrip_is_identity() {
        let c = cmd();
        let cap = issue_capability(&seed(9), &c);
        let p = AuthMsg::Propose(propose(&seed(1), 3, c.clone(), cap));
        let v = AuthMsg::Vote(vote(&seed(2), 3, &c));
        let cm = AuthMsg::Commit(Commit {
            slot: 3,
            cmd: c,
            qc: QuorumCert {
                votes: vec![vote(&seed(1), 3, &cmd()), vote(&seed(2), 3, &cmd())],
            },
        });
        for m in [p, v, cm] {
            assert_eq!(decode_msg(&encode_msg(&m)).unwrap(), m);
        }
    }

    /// THE load-bearing property: a message that verified before encoding still
    /// verifies after a wire round-trip. A codec that perturbed the term bytes
    /// would round-trip the struct yet break authentication — this is what
    /// catches that.
    #[test]
    fn roundtrip_preserves_verification() {
        let r = roster3();
        let c = cmd();
        let cap = issue_capability(&seed(9), &c);

        let p = propose(&seed(1), 0, c.clone(), cap);
        assert!(verify_proposal(&p, &r));
        let AuthMsg::Propose(p2) = decode_msg(&encode_msg(&AuthMsg::Propose(p))).unwrap() else {
            panic!("tag drifted");
        };
        assert!(
            verify_proposal(&p2, &r),
            "proposal must still verify after round-trip"
        );

        let v = vote(&seed(2), 0, &c);
        assert!(verify_vote(&v, 0, &c, &r));
        let AuthMsg::Vote(v2) = decode_msg(&encode_msg(&AuthMsg::Vote(v))).unwrap() else {
            panic!("tag drifted");
        };
        assert!(
            verify_vote(&v2, 0, &c, &r),
            "vote must still verify after round-trip"
        );

        let cm = Commit {
            slot: 0,
            cmd: c.clone(),
            qc: QuorumCert {
                votes: vec![vote(&seed(1), 0, &c), vote(&seed(2), 0, &c)],
            },
        };
        assert!(verify_commit(&cm, &r));
        let AuthMsg::Commit(cm2) = decode_msg(&encode_msg(&AuthMsg::Commit(cm))).unwrap() else {
            panic!("tag drifted");
        };
        assert!(
            verify_commit(&cm2, &r),
            "commit must still verify after round-trip"
        );
    }

    /// A truncated / garbage frame is a clean error, not a panic.
    #[test]
    fn malformed_frames_are_rejected() {
        assert!(decode_msg(&[]).is_err());
        assert!(decode_msg(&[0xff, 0x00, 0x13]).is_err());
        // A valid CBOR value of the wrong shape (an integer, not [tag, body]).
        let mut buf = Vec::new();
        ciborium::into_writer(&Value::Integer(5.into()), &mut buf).unwrap();
        assert!(decode_msg(&buf).is_err());
    }

    /// A flipped byte in the encoded term must not decode into a DIFFERENT valid,
    /// verifying message — either it fails to decode, or it decodes to something
    /// whose signature no longer checks. Corruption must never pass silently.
    #[test]
    fn corruption_never_passes_verification() {
        let r = roster3();
        let c = cmd();
        let v = vote(&seed(2), 0, &c);
        let bytes = encode_msg(&AuthMsg::Vote(v));

        let mut caught = 0;
        for i in 0..bytes.len() {
            let mut b = bytes.clone();
            b[i] ^= 0x01;
            match decode_msg(&b) {
                Err(_) => caught += 1,
                Ok(AuthMsg::Vote(v2)) => {
                    // Decoded, so it must NOT verify (unless the flip was a no-op
                    // that produced the identical message).
                    if v2 == vote(&seed(2), 0, &c) {
                        caught += 1; // identical message — a benign re-encoding
                    } else {
                        assert!(
                            !verify_vote(&v2, 0, &c, &r),
                            "a corrupted frame decoded to a DIFFERENT verifying vote at byte {i}"
                        );
                        caught += 1;
                    }
                }
                Ok(_) => panic!("tag corruption produced a different message kind at byte {i}"),
            }
        }
        assert_eq!(caught, bytes.len());
    }
}
