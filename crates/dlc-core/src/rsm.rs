//! The pure replicated-state-machine operational layer — mirror of
//! `lean/DLCD/Rsm.lean` (§1–§3) and the append-only `commit`
//! (`lean/DLCD/CapSafety.lean`).
//!
//! # Why this lives in `dlc-core`
//!
//! This module is the reducer-dependent RSM *transition core*: `apply_command`
//! normalizes `payload store` via [`crate::reduce::reduce_with_fuel`]. Charon
//! exposes only *optimized* MIR for **dependency** crates, so when this code
//! lived in the separate `dlc-d-rsm` crate its call to the reducer translated to
//! an *opaque axiom* (`reduce_with_fuel` in `FunsExternal`) — killing the R2
//! correspondence at the leaf. Relocated here, the reducer and the transition
//! functions are in the SAME primary Charon/Aeneas tree (`DlcCore`), so
//! `apply_command` calls the *real body* of `reduce_with_fuel`.
//!
//! The consensus *predicates* (`is_quorum`, `decided`) stay in the `dlc-d-rsm`
//! crate, which now path-depends on this module for `Command` et al.
//!
//! # The same hard fence as the rest of `dlc-core`
//!
//!   * No trait objects (`dyn Trait`); no `async` / futures.
//!   * No closures in translation-visible code — folds and maps are written as
//!     explicit indexed `for` loops (the Charon/Aeneas soft-spot): `world_step`
//!     and `apply_prefix` emit `*_loop` bodies, not captured-closure `.map`.
//!   * No third-party deps (only `core`, `alloc`); no `unsafe`.
//!
//! # Scope
//!
//! This is the *operational* mirror + translation target. The machine-checked
//! refinement `Rust world_step ≡ Lean worldStep` (and the transport of the
//! guarantees G1–G4 through it) is `Prop`-layer work in `lean/DLCD/`; nothing
//! here claims the Rust core "satisfies G1–G4".
//!
//! # The capability fence
//!
//! `Command` carries an opaque `cap` slot and `commit` is append-only; the
//! capability side-condition (`auth : Deriv (issuer says writeCap)`) and the
//! non-interference guarantees are `Prop`-level facts about *derivations*, not
//! runtime data. The Rust core carries the `Command` but not its `Deriv`; the
//! authority check is discharged at the `Prop` layer, never re-established here.

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::reduce::reduce_with_fuel;
use crate::syntax::{Prop, Term};

// ----------------------------------------------------------------------------
// §1 — the failure-model contract (mirror of `DLCD.FailureBudget`).
// ----------------------------------------------------------------------------

/// The failure-model contract the slice's guarantees are relative to.
///
/// `FailureBudget` mirrors the `DLC.DpBudget` graded-comonad template
/// (`zero`/`saturating_add`/`le`): a declared crash-fault tolerance `f` and a
/// `fair_delivery` assumption, plus a *consumable* grade `consumed` counting
/// crash faults charged so far. `within_contract` is the enforced predicate —
/// the slice's guarantees are stated relative to it. Lean uses `Nat`; the Rust
/// image narrows to `u32` (the Aeneas `U32`↔`Nat` fence is discharged at the
/// `Prop` layer, not here).
///
/// Mirror of `DLCD.FailureBudget`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailureBudget {
    /// Maximum tolerated crash faults (the `f` of an `f`-resilient protocol).
    pub max_faults: u32,
    /// The fair-delivery assumption: every message sent to a correct replica
    /// is eventually delivered. An *external* assumption in Phase 1.0.
    pub fair_delivery: bool,
    /// Consumable grade: crash faults charged against the contract so far.
    /// Mirrors `DpBudget`'s consumed grade.
    pub consumed: u32,
}

impl FailureBudget {
    /// The zero grade: an `f`-resilient, fair-delivery contract with no faults
    /// charged yet. Mirror of `DLCD.FailureBudget.zero`.
    pub fn zero(f: u32) -> FailureBudget {
        FailureBudget {
            max_faults: f,
            fair_delivery: true,
            consumed: 0,
        }
    }

    /// Charge additional consumed faults (monotone, like DP sequential
    /// composition on the grade). Mirror of `DLCD.FailureBudget.saturatingAdd`
    /// (whose Lean body is `consumed + extra`).
    pub fn saturating_add(&self, extra: u32) -> FailureBudget {
        FailureBudget {
            max_faults: self.max_faults,
            fair_delivery: self.fair_delivery,
            consumed: self.consumed + extra,
        }
    }

    /// Within-budget iff the charged faults have not exceeded the tolerated
    /// bound. Mirror of `DLCD.FailureBudget.le` (`decide (consumed ≤ maxFaults)`).
    pub fn le(&self) -> bool {
        self.consumed <= self.max_faults
    }

    /// The declared contract holds: fair delivery is assumed and the crash-fault
    /// budget is not overspent. Mirror of `DLCD.FailureBudget.withinContract`.
    pub fn within_contract(&self) -> bool {
        self.fair_delivery && self.le()
    }
}

// ----------------------------------------------------------------------------
// §2 — commands, replicas, the committed log, the global config
//      (mirror of `DLCD.Command` / `Replica` / `CommittedLog` / `GlobalConfig`).
// ----------------------------------------------------------------------------

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
/// obligation (see the module-level docs), fenced out of the Rust core.
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

// ----------------------------------------------------------------------------
// §3 — deterministic command application, the world step, append-only commit
//      (mirror of `DLCD.applyCommand` / `applyPrefix` / `deliver` / `worldStep`
//       and `DLCD.CapSafety.commit`).
// ----------------------------------------------------------------------------

/// Apply a command to a store: run DLC reduction on `payload store` to a normal
/// form (bounded by `APPLY_FUEL`). Deterministic — `reduce_with_fuel` is a
/// function and `step` is deterministic — so this is the deterministic
/// transition function SMR convergence needs.
///
/// Mirror of `DLCD.applyCommand`:
/// `(reduceWithFuel (Term.app c.payload s) applyFuel).1`. Calls
/// [`crate::reduce::reduce_with_fuel`] DIRECTLY (same crate → primary Charon
/// tree → *real body*, not an opaque axiom). `.0` is the reduced term.
pub fn apply_command(c: &Command, s: &Term) -> Term {
    let redex = Term::App(Box::new(c.payload.clone()), Box::new(s.clone()));
    reduce_with_fuel(&redex, APPLY_FUEL).0
}

/// The deterministic fold of a *committed prefix* onto an initial store. This
/// is the whole of the replica's state as a function of what it applied.
///
/// Mirror of `DLCD.applyPrefix` (`cmds.foldl (fun s c => applyCommand c s) init`).
/// Written as an explicit indexed loop (closure-free) rather than `iter().fold`.
///
/// The `needless_range_loop` allow is load-bearing, not laziness: clippy's
/// suggested `for c in cmds` iterator form is exactly the shape the Aeneas fence
/// forbids (iterator/closure-based folds translate to opaque axioms), and taking
/// the suggestion would break the R2 correspondence at this leaf. CI runs clippy
/// with `-D warnings`, so the allow has to be explicit.
#[allow(clippy::needless_range_loop)]
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
/// whose *capturing* closure (`g.log`) is the Charon/Aeneas soft-spot. The
/// loop emits a `world_step_loop` in the Aeneas image.
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

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::vec;

    use crate::rsm::{
        apply_command, apply_prefix, commit, deliver, world_step, Command, FailureBudget,
        GlobalConfig, Replica,
    };
    use crate::syntax::{Prop, Term};

    /// The anti-vacuity `dup` command — `λ_:atom0. ⟨x, x⟩` — mirroring
    /// `DLCD.RsmAntiVacuity.dup`. Applied to `var 0` it reduces to
    /// `⟨var 0, var 0⟩`: the store genuinely CHANGES (distinct head
    /// constructor), so convergence is not observed over a no-op.
    fn dup() -> Command {
        Command {
            payload: Term::Lam(
                Box::new(Prop::Atom(0)),
                Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
            ),
            cap: None,
        }
    }

    /// The shared initial store — mirror of `DLCD.RsmAntiVacuity.init`.
    fn init() -> Term {
        Term::Var(0)
    }

    /// The transformed store `⟨var 0, var 0⟩`.
    fn changed() -> Term {
        Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))
    }

    /// `apply_command dup init` really changes the store: `var 0 ↦ ⟨var 0, var
    /// 0⟩` (mirror of the Lean `example : applyCommand dup init = ..` at
    /// `Rsm.lean` L254).
    #[test]
    fn apply_command_changes_store() {
        assert_eq!(apply_command(&dup(), &init()), changed());
        assert_ne!(apply_command(&dup(), &init()), init());
    }

    /// `apply_prefix` folds the one-slot log to the changed store.
    #[test]
    fn apply_prefix_one_slot() {
        let log = vec![dup()];
        assert_eq!(apply_prefix(&init(), &log), changed());
    }

    /// Two replicas that each deliver the single committed slot converge on the
    /// SAME store — and it is the *changed* `⟨var 0, var 0⟩`, not the initial
    /// `var 0`. This is the Rust image of `DLCD.RsmAntiVacuity.converge` +
    /// `converged_store_changed`.
    #[test]
    fn two_replicas_converge_on_prefix() {
        let log = vec![dup()];
        let r1 = deliver(&log, &Replica { id: 0, store: init(), applied: 0 });
        let r2 = deliver(&log, &Replica { id: 1, store: init(), applied: 0 });
        assert_eq!(r1.store, r2.store);
        assert_eq!(r1.store, changed());
        assert_ne!(r1.store, init());
        assert_eq!(r1.applied, 1);
        assert_eq!(r2.applied, 1);
    }

    /// A concrete 2-replica run through the FULL transition surface: commit an
    /// authorized-shaped command (carrying a non-`None` `cap`) onto a fresh
    /// config, then `world_step` all replicas and observe convergence.
    #[test]
    fn world_step_two_replica_run() {
        // An "authorized-shaped" command: same operational payload, but with a
        // (Phase-1.0-opaque) capability slot populated. The Rust core carries
        // `cap` without enforcing it (the fence); commit is append-only.
        let authorized = Command {
            payload: dup().payload,
            cap: Some(Prop::Atom(7)),
        };

        let g0 = GlobalConfig {
            replicas: vec![
                Replica { id: 0, store: init(), applied: 0 },
                Replica { id: 1, store: init(), applied: 0 },
            ],
            log: vec![],
            budget: FailureBudget::zero(1),
        };

        // Commit appends to the log; replicas are untouched by commit.
        let g1 = commit(&g0, authorized);
        assert_eq!(g1.log.len(), 1);
        assert_eq!(g1.replicas.len(), 2);
        assert!(g1.budget.within_contract());

        // One world step: every replica delivers slot 0.
        let g2 = world_step(&g1);
        assert_eq!(g2.replicas[0].store, changed());
        assert_eq!(g2.replicas[1].store, changed());
        // Convergence: both replicas hold the SAME, CHANGED store.
        assert_eq!(g2.replicas[0].store, g2.replicas[1].store);
        assert_ne!(g2.replicas[0].store, init());
        assert_eq!(g2.replicas[0].applied, 1);

        // A second world step is a no-op: nothing more is committed.
        let g3 = world_step(&g2);
        assert_eq!(g3.replicas[0].store, g2.replicas[0].store);
        assert_eq!(g3.replicas[0].applied, 1);
    }

    /// The failure-model contract behaves like the Lean `FailureBudget`.
    #[test]
    fn failure_budget_contract() {
        let b = FailureBudget::zero(2);
        assert!(b.within_contract());
        assert!(b.le());
        // Charge within budget: still within contract.
        let b1 = b.saturating_add(2);
        assert!(b1.within_contract());
        // Overspend: budget exceeded, contract broken.
        let b2 = b.saturating_add(3);
        assert!(!b2.le());
        assert!(!b2.within_contract());
    }
}
