//! DLC-D consensus surface — the decidable quorum/decision predicates.
//!
//! This crate carries the *decidable* content of `lean/DLCD/Consensus.lean`:
//! the strict-majority quorum test `is_quorum` and the `decided` witness. The
//! reducer-dependent RSM **transition core** (`FailureBudget`, `Command`,
//! `Replica`, `GlobalConfig`, `apply_command`, `apply_prefix`, `deliver`,
//! `world_step`, `commit`, `APPLY_FUEL`) now lives in
//! [`dlc_core::rsm`](../dlc_core/rsm/index.html).
//!
//! # Why the transition core moved to `dlc-core` (Arch-1)
//!
//! `apply_command` normalizes `payload store` via
//! `dlc_core::reduce::reduce_with_fuel`. Charon exposes only *optimized* MIR for
//! **dependency** crates, so translating the transition core *here* (with
//! `dlc-core` as a dependency) produced an *opaque axiom* for the reducer
//! (`[Error] There should be no bottoms` / `reduce_with_fuel` in
//! `FunsExternal`), killing the R2 correspondence at the leaf. The core was
//! relocated into `dlc-core` so the reducer and the transition functions are in
//! ONE primary Charon/Aeneas tree (`lean/DLC/Aeneas/DlcCore`), where
//! `apply_command` calls the reducer's *real body*. This crate stays alive for
//! the consensus predicates and re-imports `dlc_core::rsm::Command`.
//!
//! # The same hard fence as `dlc-core`
//!
//!   * No trait objects (`dyn Trait`); no `async` / futures.
//!   * No closures in translation-visible code — `decided` counts votes with an
//!     explicit indexed `for` loop (the Charon/Aeneas soft-spot), not
//!     `iter().filter().count()`.
//!   * No third-party dependencies. Only `core`, `alloc`, and `dlc-core`.
//!   * No `unsafe`.
//!
//! Its Lean image lands at `lean/DLCD/Aeneas/DlcDRsm/` and is drift-gated
//! against this source by `scripts/check-drift.sh`. Because it path-depends on
//! `dlc-core`, its single `dlc_d_rsm.llbc` INLINES the `dlc_core.*` items the
//! consensus predicates reference (`Command`), so the tree stays self-contained.
//!
//! # Scope
//!
//! The `Finset`/`Fin n` `Prop` forms of consensus (`agreement`,
//! `quorum_intersect`, `validity`, `committed_prefix_agree`) stay Lean-only —
//! they are the *guarantees* the Rust core must be shown to *serve*, not code to
//! translate. This crate ships no correspondence proof (that is R2.2–R2.4).

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate alloc;

pub mod consensus;

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::vec;

    use dlc_core::rsm::Command;
    use dlc_core::syntax::{Prop, Term};

    use crate::consensus::{decided, is_quorum};

    /// The anti-vacuity `dup` command — `λ_:atom0. ⟨x, x⟩` — mirroring
    /// `DLCD.RsmAntiVacuity.dup`. Reused here to build distinct votes.
    fn dup() -> Command {
        Command {
            payload: Term::Lam(
                Box::new(Prop::Atom(0)),
                Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
            ),
            cap: None,
        }
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
