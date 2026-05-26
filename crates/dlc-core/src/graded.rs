//! Graded comonad for quantitative obligations (differential-privacy budgets).
//!
//! Following the categorical model of Petricek-Mycroft-Orchard (graded
//! comonads) and the recent applied work in *Graded Modal Types for
//! Integrity and Confidentiality* (arXiv 2309.04324), we pair a proposition
//! with a *grade* drawn from an ordered monoid. For DP, the grade is a
//! `(ε, δ)`-budget and the monoid operation is componentwise addition.
//!
//! In DLC the graded comonad shows up two places:
//!   * As the runtime carrier for `□_{ε-DP(δ)} φ` — the proof of `φ` is
//!     tagged with the budget it consumed.
//!   * As the IFC bridge for quantitative non-interference (Theorem T3 in
//!     the DP setting). Mirrors the categorical structure used by nucleus
//!     in `crates/portcullis/src/graded.rs` for risk tracking.
//!
//! Comonad laws:
//!   counit / extract:   `Graded<φ, 0> -> φ`
//!   coextend / extend:  `Graded<φ, ε> -> (Graded<φ, ε> -> ψ) -> Graded<ψ, ε>`
//!   comultiply:         `Graded<φ, ε> -> Graded<Graded<φ, ε>, ε>`
//!
//! The grade-additive law: composing two graded computations adds their
//! grades, which is exactly DP's sequential-composition theorem.

use crate::obligation::DpBudget;

/// A proposition carrier paired with its consumed grade.
///
/// The phantom proposition lives at the type level via the type parameter
/// `Prop`; this module operates over arbitrary carriers so the same
/// infrastructure can also grade by IFC-label, by execution cost, etc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graded<P> {
    /// The carried value (a proof, a witness, etc.).
    pub value: P,
    /// The grade accumulated by producing this value.
    pub grade: DpBudget,
}

impl<P> Graded<P> {
    /// Wrap a value at the zero grade.
    pub fn pure(value: P) -> Self {
        Graded {
            value,
            grade: DpBudget::ZERO,
        }
    }

    /// `counit` — extract the underlying value when the grade is zero.
    /// Returns `None` if any budget has been consumed.
    pub fn counit(self) -> Result<P, Self> {
        if self.grade == DpBudget::ZERO {
            Ok(self.value)
        } else {
            Err(self)
        }
    }

    /// Map the carrier while preserving the grade. Functor action.
    pub fn map<Q, F: FnOnce(P) -> Q>(self, f: F) -> Graded<Q> {
        Graded {
            value: f(self.value),
            grade: self.grade,
        }
    }

    /// Sequence: tack on additional budget consumption to an already-graded
    /// computation. The grade adds (DP sequential composition).
    pub fn consume(self, additional: DpBudget) -> Self {
        Graded {
            value: self.value,
            grade: self.grade.saturating_add(additional),
        }
    }

    /// Check the accumulated grade against a budget ceiling.
    pub fn within_budget(&self, ceiling: &DpBudget) -> bool {
        self.grade.leq(ceiling)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_is_zero_grade() {
        let g = Graded::pure(42u32);
        assert_eq!(g.grade, DpBudget::ZERO);
    }

    #[test]
    fn counit_recovers_value_at_zero_grade() {
        let g = Graded::pure("hello");
        assert_eq!(g.counit(), Ok("hello"));
    }

    #[test]
    fn counit_refuses_nonzero_grade() {
        let g = Graded::pure("hello").consume(DpBudget {
            epsilon_micros: 1,
            delta_micros: 0,
        });
        assert!(g.counit().is_err());
    }

    #[test]
    fn consume_is_associative() {
        // (g.consume(a)).consume(b) == g.consume(a + b)
        let eps_a = DpBudget {
            epsilon_micros: 100,
            delta_micros: 0,
        };
        let eps_b = DpBudget {
            epsilon_micros: 200,
            delta_micros: 5,
        };
        let lhs = Graded::pure(()).consume(eps_a).consume(eps_b);
        let rhs = Graded::pure(()).consume(eps_a.saturating_add(eps_b));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn within_budget_check() {
        let ceiling = DpBudget {
            epsilon_micros: 1000,
            delta_micros: 100,
        };
        let g = Graded::pure(()).consume(DpBudget {
            epsilon_micros: 500,
            delta_micros: 50,
        });
        assert!(g.within_budget(&ceiling));

        let over = g.consume(DpBudget {
            epsilon_micros: 600,
            delta_micros: 0,
        });
        assert!(!over.within_budget(&ceiling));
    }

    #[test]
    fn map_preserves_grade() {
        let g = Graded::pure(3u32).consume(DpBudget {
            epsilon_micros: 50,
            delta_micros: 0,
        });
        let mapped = g.map(|x| x * 2);
        assert_eq!(mapped.value, 6);
        assert_eq!(mapped.grade.epsilon_micros, 50);
    }
}
