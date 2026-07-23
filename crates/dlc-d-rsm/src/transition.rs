//! Deterministic command application and the world step — mirror of
//! `DLCD.applyCommand` / `applyPrefix` / `deliver` / `worldStep` and the
//! append-only `commit` (`lean/DLCD/Rsm.lean` §3 + `DLCD.CapSafety.commit`).
//!
//! **Aeneas-clean discipline.** `apply_prefix` and `world_step` are written as
//! explicit indexed `for` loops, NOT `.iter().fold`/`.iter().map` with a
//! captured variable: closures are the Charon/Aeneas soft-spot this crate must
//! stay translatable under. This mirrors `dlc_core::reduce::reduce_with_fuel`'s
//! own discipline (`for n in 0..fuel { .. }`, explicit `match`, no `Option::map`).

use alloc::boxed::Box;
use alloc::vec::Vec;

use dlc_core::reduce::reduce_with_fuel;
use dlc_core::syntax::Term;

use crate::state::{Command, CommittedLog, GlobalConfig, Replica, APPLY_FUEL};

/// Apply a command to a store: run DLC reduction on `payload store` to a normal
/// form (bounded by `APPLY_FUEL`). Deterministic — `reduce_with_fuel` is a
/// function and `step` is deterministic — so this is the deterministic
/// transition function SMR convergence needs.
///
/// Mirror of `DLCD.applyCommand`:
/// `(reduceWithFuel (Term.app c.payload s) applyFuel).1`. Reuses
/// `dlc_core::reduce::reduce_with_fuel` (`.0` = the reduced term).
pub fn apply_command(c: &Command, s: &Term) -> Term {
    let redex = Term::App(Box::new(c.payload.clone()), Box::new(s.clone()));
    reduce_with_fuel(&redex, APPLY_FUEL).0
}

/// The deterministic fold of a *committed prefix* onto an initial store. This
/// is the whole of the replica's state as a function of what it applied.
///
/// Mirror of `DLCD.applyPrefix` (`cmds.foldl (fun s c => applyCommand c s) init`).
/// Written as an explicit indexed loop (closure-free) rather than `iter().fold`.
pub fn apply_prefix(init: &Term, cmds: &[Command]) -> Term {
    let mut acc = init.clone();
    for i in 0..cmds.len() {
        acc = apply_command(&cmds[i], &acc);
    }
    acc
}

/// Deliver the next committed slot to a replica: advance `applied` and apply
/// `log[applied]`. If the replica is caught up to the committed log, it is a
/// no-op (nothing more is committed yet).
///
/// Mirror of `DLCD.deliver` (`match log[r.applied]? with ..`). Uses `Vec::get`
/// (returns `Option`) and an explicit `match` — no closure.
pub fn deliver(log: &CommittedLog, r: &Replica) -> Replica {
    match log.get(r.applied as usize) {
        Some(c) => Replica {
            id: r.id,
            store: apply_command(c, &r.store),
            applied: r.applied + 1,
        },
        None => r.clone(),
    }
}

/// One world step: every replica delivers its next committed slot. (Which
/// replicas step, and message loss/reordering, live under the `FailureBudget`
/// contract; the fair-delivery assumption guarantees each correct replica
/// *eventually* advances.)
///
/// Mirror of `DLCD.worldStep` (`{ g with replicas := g.replicas.map (deliver
/// g.log) }`). Written as an explicit indexed `for` loop building the new
/// replica vector — deliberately NOT `.iter().map(|r| deliver(&g.log, r))`,
/// whose *capturing* closure (`g.log`) is the Charon/Aeneas soft-spot.
pub fn world_step(g: &GlobalConfig) -> GlobalConfig {
    let mut stepped: Vec<Replica> = Vec::new();
    for i in 0..g.replicas.len() {
        stepped.push(deliver(&g.log, &g.replicas[i]));
    }
    GlobalConfig {
        replicas: stepped,
        log: g.log.clone(),
        budget: g.budget.clone(),
    }
}

/// Append-only commit: extend the committed log with one more command.
///
/// Mirror of the OPERATIONAL core of `DLCD.commit` (`CapSafety.lean`). The
/// capability side-condition (`auth : Deriv (issuer says writeCap)`) is a
/// *typing* obligation, NOT runtime data: the Rust `commit` carries the
/// `Command` (including its opaque `cap` slot) and appends it; the authority
/// check is discharged at the `Prop` layer, not enforced here.
pub fn commit(g: &GlobalConfig, c: Command) -> GlobalConfig {
    let mut log = g.log.clone();
    log.push(c);
    GlobalConfig {
        replicas: g.replicas.clone(),
        log,
        budget: g.budget.clone(),
    }
}
