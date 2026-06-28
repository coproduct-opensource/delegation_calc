//! The DP budget as a `coproduct_algebra::Quantale` — the **additive (non-idempotent)** instance.
//!
//! `dlc-core`'s `DpBudget` already composes by `saturating_add` (the DP sequential-composition
//! theorem; see `graded::Graded::consume`). That is exactly a quantale tensor — but additive, not
//! `meet`, which is what distinguishes a real quantale from a frame. We expose it here (not in the
//! zero-dep kernel) as `Spend`, a newtype, for two reasons:
//!
//! 1. **Orientation (Lawvere).** A quantale's order must make the tensor's *absorbing* element the
//!    bottom: more-consumed is *lower*, so the saturation point (`u64::MAX`) is `⊥` (exhausted) and
//!    `ZERO` is `⊤`. Then `a ⊗ ⊥ = ⊥` (saturating add) and `tensor_all` over a pipeline totals its
//!    budget — `⊥` meaning "ceiling blown."
//! 2. **No `leq` collision.** `DpBudget::leq` is the *opposite* order ("is-under-ceiling", numeric).
//!    Implementing `Lattice` directly on `DpBudget` would give it a second, contradictory `leq`.
//!    The newtype keeps the kernel's API intact.
//!
//! This is the third independent adopter of `Quantale` (with trust-atlas `Maturity` and
//! remediation-engine `MaturityRank`, both `meet`-quantales), and the only additive one — so the
//! trait is shown to carry both shapes on real types, not just in the substrate's own tests.

use coproduct_algebra::{BoundedLattice, Lattice, Quantale};
use dlc_core::obligation::DpBudget;

/// `DpBudget` under the spend order: a quantale whose tensor is DP sequential composition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Spend(pub DpBudget);

impl Spend {
    /// The exhausted budget — the tensor's absorbing element and the lattice bottom.
    pub const EXHAUSTED: Spend = Spend(DpBudget {
        epsilon_micros: u64::MAX,
        delta_micros: u64::MAX,
    });
}

impl Lattice for Spend {
    fn meet(&self, other: &Self) -> Self {
        // inf in the spend order = the MORE-consumed budget (componentwise max).
        Spend(DpBudget {
            epsilon_micros: self.0.epsilon_micros.max(other.0.epsilon_micros),
            delta_micros: self.0.delta_micros.max(other.0.delta_micros),
        })
    }
    fn join(&self, other: &Self) -> Self {
        // sup in the spend order = the LESS-consumed budget (componentwise min); "best across paths".
        Spend(DpBudget {
            epsilon_micros: self.0.epsilon_micros.min(other.0.epsilon_micros),
            delta_micros: self.0.delta_micros.min(other.0.delta_micros),
        })
    }
    fn leq(&self, other: &Self) -> bool {
        // self ≤ other  ⟺  self has consumed at least as much (reversed numeric order).
        self.0.epsilon_micros >= other.0.epsilon_micros
            && self.0.delta_micros >= other.0.delta_micros
    }
}

impl BoundedLattice for Spend {
    fn top() -> Self {
        Spend(DpBudget::ZERO) // nothing spent
    }
    fn bottom() -> Self {
        Spend::EXHAUSTED
    }
}

impl Quantale for Spend {
    fn unit() -> Self {
        Spend(DpBudget::ZERO)
    }
    fn tensor(&self, other: &Self) -> Self {
        // DP sequential composition — the same `saturating_add` the graded comonad's `consume` uses.
        Spend(self.0.saturating_add(other.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use coproduct_algebra::tensor_all;
    use dlc_core::graded::Graded;

    fn b(epsilon_micros: u64, delta_micros: u64) -> Spend {
        Spend(DpBudget {
            epsilon_micros,
            delta_micros,
        })
    }

    #[test]
    fn dp_budget_is_a_quantale() {
        let samples = [
            Spend(DpBudget::ZERO),
            b(100, 0),
            b(0, 5),
            b(1_000, 100),
            b(u64::MAX - 1, 7),
        ];
        assert!(coproduct_algebra::verify_quantale_laws(&samples).is_empty());
        // additive, hence NOT idempotent — this is a genuine quantale, not a frame.
        assert_ne!(b(40, 0).tensor(&b(40, 0)), b(40, 0));
    }

    #[test]
    fn tensor_is_dp_sequential_composition() {
        // tensor_all totals a pipeline's budget …
        assert_eq!(tensor_all([b(100, 0), b(200, 5), b(50, 1)]), b(350, 6));
        // … and agrees with the kernel's own graded-comonad `consume` chain.
        let g = Graded::pure(())
            .consume(DpBudget { epsilon_micros: 100, delta_micros: 0 })
            .consume(DpBudget { epsilon_micros: 200, delta_micros: 5 });
        assert_eq!(Spend(g.grade), b(300, 5));
        // spending past saturation lands on ⊥ (ceiling blown) and stays.
        assert_eq!(b(u64::MAX, 0).tensor(&b(1, 0)), b(u64::MAX, 0));
    }
}
