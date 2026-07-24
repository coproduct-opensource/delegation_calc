//! The async transport for the authenticated node — `AuthNode` over `tokio`,
//! every message crossing the channel as ENCODED BYTES.
//!
//! Design: `spec/r6-1b-replication-protocol.md` §6.3. This is what makes the
//! [`crate::codec`] load-bearing on a live path rather than a library exercised
//! only by its own tests: peers exchange `Vec<u8>` frames and each decodes with
//! [`crate::codec::decode_msg`] before handing the [`crate::auth::AuthMsg`] to
//! its [`AuthNode`]. A frame that fails to decode is dropped, exactly as a
//! networked node would drop a malformed packet.
//!
//! It is the async sibling of the deterministic in-memory harness in
//! `auth.rs`'s tests: that one proves the protocol; this one proves the protocol
//! *plus the codec* over concurrent tasks. Channels stand in for sockets — the
//! bytes on the channel are exactly the bytes a socket would carry, so swapping
//! in TCP is a carrier change, not a protocol change. Fair, loss-free delivery
//! is provided by the channel (the model's `fair_delivery` assumption), not
//! proved; it is in the TCB, as in `net.rs` §5.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use dlc_core::rsm::{Command, FailureBudget, GlobalConfig};
use dlc_core::syntax::Term;
use tokio::sync::mpsc::{unbounded_channel, UnboundedSender};
use tokio::task::JoinSet;

use crate::auth::{AuthNode, Dest};
use crate::codec::{decode_msg, encode_msg};
use crate::proto::{Capability, Roster};

/// How an authenticated cluster run is configured.
#[derive(Clone)]
pub struct AuthClusterConfig {
    /// One signing seed per replica; `seeds[i]` owns roster seat `i`.
    pub seeds: Vec<[u8; 32]>,
    /// The pinned committee (must match `seeds`).
    pub roster: Roster,
    /// The static leader's roster index.
    pub leader: u32,
    /// Shared initial store.
    pub init: Term,
    /// Commands to drive, each with its capability credential.
    pub workload: Vec<(Command, Capability)>,
    /// Replicas that never start — crash faults.
    pub crashed: Vec<u32>,
    /// The declared failure contract.
    pub budget: FailureBudget,
    /// How long to wait before declaring the run stalled (a legitimate outcome).
    pub settle: Duration,
}

/// What an authenticated cluster run produced.
#[derive(Clone, Debug)]
pub struct AuthOutcome {
    /// Final model view per live replica, keyed by roster index.
    pub views: BTreeMap<u32, GlobalConfig>,
    /// Every live replica applied the whole workload.
    pub complete: bool,
}

impl AuthOutcome {
    /// The live replicas' stores, in index order.
    pub fn stores(&self) -> Vec<Term> {
        self.views
            .values()
            .map(|v| v.replicas[0].store.clone())
            .collect()
    }

    /// Every live replica holds the same store (true of a stalled cluster too).
    pub fn converged(&self) -> bool {
        let mut it = self.views.values();
        match it.next() {
            None => true,
            Some(first) => it.all(|v| v.replicas[0].store == first.replicas[0].store),
        }
    }

    /// Committed slots (max over live replicas).
    pub fn committed(&self) -> usize {
        self.views.values().map(|v| v.log.len()).max().unwrap_or(0)
    }
}

/// Run an authenticated cluster over tokio, frames crossing as bytes, and report
/// the final state.
pub async fn run_auth_cluster(cfg: AuthClusterConfig) -> AuthOutcome {
    let n = cfg.seeds.len();
    let expected = cfg.workload.len();

    // One byte-carrying channel per live replica.
    let mut senders: Vec<Option<UnboundedSender<Vec<u8>>>> = Vec::with_capacity(n);
    let mut receivers = Vec::with_capacity(n);
    for idx in 0..n as u32 {
        if cfg.crashed.contains(&idx) {
            senders.push(None);
            receivers.push(None);
        } else {
            let (tx, rx) = unbounded_channel::<Vec<u8>>();
            senders.push(Some(tx));
            receivers.push(Some(rx));
        }
    }
    let senders = Arc::new(senders);
    let snapshots: Arc<Mutex<BTreeMap<u32, GlobalConfig>>> = Arc::new(Mutex::new(BTreeMap::new()));

    let mut tasks = JoinSet::new();
    for (idx, rx) in receivers.into_iter().enumerate() {
        let Some(mut rx) = rx else { continue };
        let idx = idx as u32;
        let senders = Arc::clone(&senders);
        let snapshots = Arc::clone(&snapshots);
        let cfg = cfg.clone();

        tasks.spawn(async move {
            let mut node = AuthNode::new(
                cfg.seeds[idx as usize],
                cfg.roster.clone(),
                idx,
                cfg.leader,
                cfg.init.clone(),
                cfg.budget.clone(),
            )
            .expect("seed matches roster seat");
            let mut next_cmd = 0usize;
            publish(&snapshots, idx, &node);

            // Leader drives the workload one slot at a time.
            let outs = drive(&mut node, &mut next_cmd, &cfg.workload);
            dispatch(&senders, idx, outs);
            publish(&snapshots, idx, &node);

            while (node.applied() as usize) < expected {
                let Some(frame) = rx.recv().await else { break };
                // Decode at the wire boundary — a malformed frame is dropped.
                let Ok(msg) = decode_msg(&frame) else {
                    continue;
                };
                let outs = node.handle(msg);
                dispatch(&senders, idx, outs);
                publish(&snapshots, idx, &node);

                let outs = drive(&mut node, &mut next_cmd, &cfg.workload);
                dispatch(&senders, idx, outs);
                publish(&snapshots, idx, &node);
            }
        });
    }

    let settled = tokio::time::timeout(cfg.settle, async {
        while tasks.join_next().await.is_some() {}
    })
    .await
    .is_ok();
    tasks.abort_all();

    let views = snapshots.lock().expect("snapshot mutex").clone();
    let complete = settled
        && views
            .values()
            .all(|v| v.replicas[0].applied as usize == expected);
    AuthOutcome { views, complete }
}

/// Leader-side workload driver — open the next slot once the previous landed
/// locally. Loops because a one-node cluster decides inside `submit`.
fn drive(
    node: &mut AuthNode,
    next_cmd: &mut usize,
    workload: &[(Command, Capability)],
) -> Vec<crate::auth::Out> {
    let mut outs = Vec::new();
    while node.is_leader()
        && *next_cmd < workload.len()
        && node.log().len() == *next_cmd
        && (node.applied() as usize) == *next_cmd
    {
        let (cmd, cap) = workload[*next_cmd].clone();
        outs.extend(node.submit(cmd, cap));
        *next_cmd += 1;
    }
    outs
}

/// ENCODE each outgoing message and deliver the bytes. Sends to a crashed
/// replica fail and are dropped (crash-stop).
fn dispatch(senders: &[Option<UnboundedSender<Vec<u8>>>], from: u32, outs: Vec<crate::auth::Out>) {
    for out in outs {
        let frame = encode_msg(&out.msg);
        match out.dest {
            Dest::Peers => {
                for (idx, tx) in senders.iter().enumerate() {
                    if idx as u32 == from {
                        continue;
                    }
                    if let Some(tx) = tx {
                        let _ = tx.send(frame.clone());
                    }
                }
            }
            Dest::To(idx) => {
                if let Some(Some(tx)) = senders.get(idx as usize) {
                    let _ = tx.send(frame.clone());
                }
            }
        }
    }
}

fn publish(snapshots: &Arc<Mutex<BTreeMap<u32, GlobalConfig>>>, idx: u32, node: &AuthNode) {
    snapshots
        .lock()
        .expect("snapshot mutex")
        .insert(idx, node.view().clone());
}
