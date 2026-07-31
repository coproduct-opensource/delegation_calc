//! Linear obligations.
//!
//! Once discharged, consumed — this is what makes obligation tracking sound
//! across reduction (T4). The production realization mirrors nucleus's
//! `DischargedBundle` sealed-constructor pattern: a `Discharged<O>` value is
//! constructible only by going through the discharge typing rule, so its mere
//! existence is computational evidence that `O` was satisfied.

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::principal::Principal;
use crate::time::TimeBound;

/// An obligation expression.
///
/// Linear in the substructural sense: discharge consumes a hypothesis.
/// Cf. nucleus `crates/portcullis-core/src/discharge.rs::DischargedBundle`
/// for the runtime realization at M3.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obligation {
    /// ⊤ — trivially discharged.
    Top,
    /// ⊥ — un-dischargeable; presence forces non-progress.
    Bot,
    /// `act_of(p, action)` — principal p must perform `action`.
    ActOf(Principal, ActionId),
    /// `within(τ)` — must be discharged before time τ.
    Within(TimeBound),
    /// `O₁ ⊗ O₂` — both must be discharged (multiplicative).
    Tensor(Box<Obligation>, Box<Obligation>),
    /// `O₁ ⊸ O₂` — discharging O₁ activates O₂ (linear implication).
    Lolli(Box<Obligation>, Box<Obligation>),
    /// `ε-DP(δ)` — quantitative DP-budget obligation. Discharge consumes
    /// `ε` of the budget `δ`. Discharge fails if remaining budget < `ε`.
    /// See `crate::graded` for the graded-comonad infrastructure.
    DpBudget(DpBudget),
}

/// Opaque identifier for an action; resolved by the runtime obligation table.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ActionId(pub Vec<u8>);

/// A differential-privacy budget grade.
///
/// `epsilon_micros` and `delta_micros` are micro-units (×10⁻⁶) so the type
/// stays integer-only — Aeneas does not yet handle floats well. Production
/// callers convert from `f64` at the boundary.
///
/// The semantics matches Dwork-Rothblum approximate DP: `(ε, δ)`-DP.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DpBudget {
    /// ε (privacy-loss bound) in micro-units.
    pub epsilon_micros: u64,
    /// δ (failure probability) in micro-units.
    pub delta_micros: u64,
}

impl DpBudget {
    /// The zero budget — no privacy budget consumed.
    pub const ZERO: DpBudget = DpBudget {
        epsilon_micros: 0,
        delta_micros: 0,
    };

    /// Compose two budgets sequentially (basic sequential-composition
    /// theorem of DP). Saturating to `u64::MAX` rather than wrapping —
    /// exceeding the budget is the *condition* the obligation discharge
    /// checks against, so silent overflow would be unsound.
    ///
    /// Named `saturating_add` (not `add`) to make the saturating semantics
    /// explicit at call sites, matching `u64::saturating_add`.
    pub fn saturating_add(self, other: Self) -> Self {
        DpBudget {
            epsilon_micros: self.epsilon_micros.saturating_add(other.epsilon_micros),
            delta_micros: self.delta_micros.saturating_add(other.delta_micros),
        }
    }

    /// Total order on budgets: `a ≤ b` iff `a.ε ≤ b.ε` AND `a.δ ≤ b.δ`.
    pub fn leq(&self, other: &Self) -> bool {
        self.epsilon_micros <= other.epsilon_micros && self.delta_micros <= other.delta_micros
    }
}

/// Evidence that an obligation has been discharged.
///
/// **Sealed:** the only way to construct a `Discharged<O>` is by going
/// through the `discharge` typing rule in `crate::judgment::Deriv`. Mere
/// existence of this value is computational evidence of discharge — this is
/// the runtime realization of `□_O φ` elimination, matching nucleus's
/// `DischargedBundle` design.
///
/// `O` is the discharged obligation expression; clients pattern-match it for
/// audit purposes but cannot fabricate a `Discharged<O>` for an obligation
/// that hasn't actually been satisfied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Discharged {
    // NOTE: field is named `obl`, not `obligation`, on purpose: the Aeneas Lean
    // translation places every item under the `obligation` module namespace, so
    // a field literally named `obligation` shadows that namespace inside the
    // generated `Discharged` structure and the `new_sealed` body, breaking
    // resolution of `obligation::Seal` / `obligation::Discharged`. Renaming the
    // private field un-shadows it. The public audit accessor is still
    // `Discharged::obligation()`, so no external API changes.
    obl: Obligation,
    // The private field plus the absence of a public constructor means only
    // `crate::judgment::discharge_check` can mint this — the only API path
    // is via the typing rule.
    _seal: Seal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Seal;

impl Discharged {
    /// Construct a `Discharged<O>` *only* from within this crate, after the
    /// typing-level checks have run. External callers must reach for the
    /// typing rules in `crate::judgment`.
    ///
    /// The first caller lands at M1.Q3.d when `discharge_check` in
    /// `crate::judgment` wires `Deriv::Discharge` into the runtime. Until
    /// then the unit tests are the only callers; mark dead-code-allowed so
    /// the seal stays compilable.
    #[allow(dead_code)]
    pub(crate) fn new_sealed(obl: Obligation) -> Self {
        Discharged { obl, _seal: Seal }
    }

    /// Inspect the obligation that was discharged. Audit-only.
    pub fn obligation(&self) -> &Obligation {
        &self.obl
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dp_budget_add_saturates() {
        let a = DpBudget {
            epsilon_micros: u64::MAX - 5,
            delta_micros: 0,
        };
        let b = DpBudget {
            epsilon_micros: 10,
            delta_micros: 0,
        };
        let sum = a.saturating_add(b);
        assert_eq!(sum.epsilon_micros, u64::MAX);
    }

    #[test]
    fn dp_budget_leq_componentwise() {
        let a = DpBudget {
            epsilon_micros: 5,
            delta_micros: 10,
        };
        let b = DpBudget {
            epsilon_micros: 10,
            delta_micros: 10,
        };
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
    }

    #[test]
    fn dp_budget_leq_is_partial() {
        // Incomparable: ε higher in a, δ higher in b.
        let a = DpBudget {
            epsilon_micros: 10,
            delta_micros: 0,
        };
        let b = DpBudget {
            epsilon_micros: 0,
            delta_micros: 10,
        };
        assert!(!a.leq(&b));
        assert!(!b.leq(&a));
    }

    #[test]
    fn discharged_preserves_obligation_for_audit() {
        let obl = Obligation::Top;
        let d = Discharged::new_sealed(obl.clone());
        assert_eq!(d.obligation(), &obl);
    }
}
