//! The failure-model contract — mirror of `DLCD.FailureBudget`
//! (`lean/DLCD/Rsm.lean` §1).
//!
//! `FailureBudget` mirrors the `DLC.DpBudget` graded-comonad template
//! (`zero`/`saturating_add`/`le`): a declared crash-fault tolerance `f` and a
//! `fair_delivery` assumption, plus a *consumable* grade `consumed` counting
//! crash faults charged so far. `within_contract` is the enforced predicate —
//! the slice's guarantees are stated relative to it. Lean uses `Nat`; the Rust
//! image narrows to `u32` (the Aeneas `U32`↔`Nat` fence is discharged at the
//! `Prop` layer, not here).

/// The failure-model contract the slice's guarantees are relative to.
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
