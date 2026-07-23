//! Commands, replicas, the committed log, and the global config — mirror of
//! `DLCD.Command` / `DLCD.Replica` / `DLCD.CommittedLog` / `DLCD.GlobalConfig`
//! (`lean/DLCD/Rsm.lean` §2).

use alloc::vec::Vec;

use dlc_core::syntax::{Prop, Term};

use crate::budget::FailureBudget;

/// Fuel bound for normalizing a command application. Fixed and global, so
/// `apply_command` is a total, deterministic function of `(Command, Term)`.
/// Mirror of `DLCD.applyFuel` — MUST equal the Lean literal `1024`.
pub const APPLY_FUEL: u32 = 1024;

/// A replicated operation: a `Term` payload to apply to the store, plus an
/// (abstract, Phase-1.0-opaque) guarding-capability / IFC-label slot that a
/// later increment will require a `CDeriv`/`says` witness for.
///
/// Mirror of `DLCD.Command`. The `cap` field is CARRIED but NOT enforced at
/// runtime: the says-typing / capability side-condition is a `Prop`-layer
/// obligation (see the crate-level docs), fenced out of the Rust core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Command {
    /// The operation, as a `Term` applied to the replica's store.
    pub payload: Term,
    /// The guarding capability / IFC label this write must eventually prove.
    /// Abstract in Phase 1.0 (`None` = unguarded skeleton write).
    pub cap: Option<Prop>,
}

/// Local register state of a single replica: its identity, its store (a `Term`
/// register value), and how far it has consumed the committed log.
///
/// Mirror of `DLCD.Replica`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replica {
    /// Replica identity.
    pub id: u32,
    /// The local register value.
    pub store: Term,
    /// Number of committed-log slots this replica has applied.
    pub applied: u32,
}

/// The totally-ordered committed sequence — the consensus output. ABSTRACT in
/// Phase 1.0: real single-decree consensus that fills each slot is a later
/// increment; here the committed log is taken as given (an oracle).
///
/// Mirror of `DLCD.CommittedLog` (`List Command` → `Vec<Command>`).
pub type CommittedLog = Vec<Command>;

/// A global configuration: the replicas, the committed log, and the failure
/// contract the guarantees are relative to.
///
/// Mirror of `DLCD.GlobalConfig`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalConfig {
    /// The replica set.
    pub replicas: Vec<Replica>,
    /// The committed, totally-ordered command log (oracle in Phase 1.0).
    pub log: CommittedLog,
    /// The declared failure-model contract.
    pub budget: FailureBudget,
}
