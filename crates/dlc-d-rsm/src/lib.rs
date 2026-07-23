//! DLC-D replicated state machine — the verified runtime core.
//!
//! This crate is the `no_std`, zero-third-party-dep, Aeneas/Charon translation
//! target that mirrors, item for item, the Lean RSM operational model
//! `lean/DLCD/Rsm.lean` (and the *decidable* surface of
//! `lean/DLCD/Consensus.lean`). Its Lean image lands at
//! `lean/DLCD/Aeneas/DlcDRsm/` and is drift-gated against this source by
//! `scripts/check-drift.sh` exactly as `dlc-core` → `lean/DLC/Aeneas/DlcCore`.
//!
//! To keep the bridge clean it stays inside the same hard fence as `dlc-core`:
//!
//!   * No trait objects (`dyn Trait`).
//!   * No `async` / futures.
//!   * No closures in translation-visible code — folds and maps are written as
//!     explicit indexed `for` loops (the Charon/Aeneas soft-spot).
//!   * No third-party dependencies. Only `core`, `alloc`, and `dlc-core`.
//!   * No `unsafe`.
//!
//! # Scope (R2.1)
//!
//! This crate is the *skeleton + translation target* only. It ships **no**
//! correspondence proof: the machine-checked refinement `Rust world_step ≡ Lean
//! worldStep` (and the transport of the guarantees G1–G4 through it) is R2.2–R2.4.
//! Nothing here claims the Rust core "satisfies G1–G4" — only that it is the
//! Aeneas-translated, drift-gated *mirror* of the proved model.
//!
//! # The capability fence
//!
//! `Command` carries an opaque `cap` slot and `commit` is append-only; the
//! capability side-condition (`auth : Deriv (issuer says writeCap)`) and the
//! non-interference guarantees are `Prop`-level facts about *derivations*, not
//! runtime data. The Rust core carries the `Command` but not its `Deriv`; the
//! authority check is discharged at the `Prop` layer, never re-established here.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate alloc;

pub mod budget;
pub mod consensus;
pub mod state;
pub mod transition;

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::vec;

    use dlc_core::syntax::{Prop, Term};

    use crate::budget::FailureBudget;
    use crate::consensus::{decided, is_quorum};
    use crate::state::{Command, GlobalConfig, Replica};
    use crate::transition::{apply_command, apply_prefix, commit, deliver, world_step};

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

    /// The decidable consensus surface: quorum test + a unanimous-quorum
    /// `decided` witness.
    #[test]
    fn consensus_surface() {
        assert!(is_quorum(2, 3)); // 4 > 3
        assert!(!is_quorum(1, 3)); // 2 > 3 is false
        assert!(is_quorum(2, 2)); // 4 > 2

        let v = dup();
        // Three replicas, two voting for `v`: a strict majority ⇒ decided.
        let votes = vec![Some(v.clone()), Some(v.clone()), None];
        assert!(decided(&votes, &v));
        // Only one vote for `v` out of three ⇒ not decided.
        let votes2 = vec![Some(v.clone()), None, None];
        assert!(!decided(&votes2, &v));
    }
}
