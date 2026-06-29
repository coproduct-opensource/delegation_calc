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

use coproduct_algebra::{BoundedLattice, Lattice, MonotoneMap, Quantale};
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

/// **Risk** grade — the additive quantale mirroring nucleus `portcullis/src/graded.rs` risk
/// tracking: risk accumulates as you compute (saturating sum), under the Lawvere spend order (more
/// risk = lower; saturation = ⊥). A single micro-unit axis. (Mirrors nucleus; the canonical home
/// would unify them, but the `τ` bridge lives next to its DP-budget endpoint `Spend`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Risk(pub u64);

impl Lattice for Risk {
    fn meet(&self, o: &Self) -> Self {
        Risk(self.0.max(o.0)) // inf in the spend order = the riskier
    }
    fn join(&self, o: &Self) -> Self {
        Risk(self.0.min(o.0)) // sup = the less-risky ("best across paths")
    }
    fn leq(&self, o: &Self) -> bool {
        self.0 >= o.0 // reversed: more risk ≤ less risk
    }
}
impl BoundedLattice for Risk {
    fn top() -> Self {
        Risk(0)
    }
    fn bottom() -> Self {
        Risk(u64::MAX)
    }
}
impl Quantale for Risk {
    fn unit() -> Self {
        Risk(0)
    }
    fn tensor(&self, o: &Self) -> Self {
        Risk(self.0.saturating_add(o.0))
    }
}

/// **τ : Risk ⇒ DpBudget** — the doctrine's long-promised risk→DP-budget change-of-base generator,
/// finally wired to real carriers. Incurred risk becomes the `ε`-budget you must account for
/// (`δ` stays 0). It is a **strict quantale homomorphism** (preserves `unit` and `⊗`, monotone),
/// so [`coproduct_algebra::change_of_base`]`(&Tau, …)` re-grades an entire risk-weighted
/// `VCategory` into DP-budget terms, preserving composition by construction.
pub struct Tau;

impl MonotoneMap<Risk, Spend> for Tau {
    fn apply(&self, r: &Risk) -> Spend {
        Spend(DpBudget {
            epsilon_micros: r.0,
            delta_micros: 0,
        })
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

    #[test]
    fn tau_is_a_strict_quantale_homomorphism() {
        let s = [Risk(0), Risk(5), Risk(100), Risk(1000), Risk(u64::MAX - 1)];
        assert!(coproduct_algebra::verify_quantale_hom(&Tau, &s).is_empty());
        assert!(coproduct_algebra::verify_monotone(&Tau, &s).is_empty());
        // incurred risk becomes ε-budget; δ stays 0.
        assert_eq!(Tau.apply(&Risk(250)), b(250, 0));
        assert_eq!(Tau.apply(&Risk(0)), b(0, 0)); // unit ↦ unit
    }

    #[test]
    fn change_of_base_regrades_a_risk_pipeline_to_dp_budget() {
        use coproduct_algebra::{change_of_base, VCategory};
        // a risk-weighted pipeline 0 →(risk 100) 1 →(risk 150) 2.
        let risk = VCategory::from_edges(3, [(0, 1, Risk(100)), (1, 2, Risk(150))]);

        // FUNCTORIALITY: τ preserves ⊗ and ∨, so regrading commutes with closure —
        // close-then-regrade == regrade-then-close. This is what makes τ a whole-system regrade,
        // not just a per-label map.
        let close_then_regrade = change_of_base(&Tau, &risk.closure());
        let regrade_then_close = change_of_base(&Tau, &risk).closure();
        assert_eq!(close_then_regrade, regrade_then_close);

        // the end-to-end DP-budget = τ of the end-to-end risk: risk along the path is the tensor
        // (saturating sum) 100 ⊗ 150 = 250, which τ sends to ε=250, δ=0.
        assert_eq!(*regrade_then_close.hom(0, 2), b(250, 0));
    }
}
