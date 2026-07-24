//! `dlc-d` — the agent authority-envelope facade.
//!
//! Re-exports the [`agent_service`] attribute macro and holds the **Tier-1 type vocabulary**
//! that turns the envelope's `cap` / `flow` / `budget` axes into ordinary `rustc` type errors:
//! a missing capability, an illegal cross-agent flow, or an over-budget fault count fails to
//! compile *before* any Tier-2 certificate check runs (spec/r6.2-agent-service-envelope.md §2, §5).
//!
//! The design mirrors the standard Rust static-IFC pattern (cf. *Cocoon*, POPL'24): security
//! labels are distinguished types and the lattice order is a trait ([`FlowsInto`]) implemented
//! exactly for the permitted edges, so an illegal flow is a trait-bound error with zero runtime
//! cost. Capabilities are phantom witnesses ([`Cap`]) whose *absence* at a write site is a type
//! error. The `budget` axis is a const generic ([`Faults`]).
//!
//! **Fences.** These types are the *build-time* claim; runtime IFC stays type-level (positioning
//! memo §5). The Tier-2 admission obligation (a real `says`-credential) is discharged separately
//! by the verified checker (`dlc_core::decide` + `rust_infer_sound`), which is where soundness
//! lives — the macro itself is out of the TCB (§3.4).

#![forbid(unsafe_code)]

use core::marker::PhantomData;

/// The `#[dlc_d::agent_service(...)]` authority-envelope macro (re-exported from `dlc-d-macro`).
pub use dlc_d_macro::agent_service;

/// The "invoke this tool" capability kind — the `C` in `Cap<C, I>`.
pub struct Invoke<T>(PhantomData<T>);

/// A capability witness: a value of `Cap<Invoke<Tool>, Issuer>` in scope proves the holder was
/// granted `Invoke<Tool>` authority by `Issuer`. The macro requires such a witness at each
/// governed write; its **absence** is a `rustc` type error (Tier-1 admission control). Minting a
/// real witness is gated on a verified `says`-credential (Tier-2) — this constructor is the
/// type-level anchor the certificate check backs.
pub struct Cap<C, I>(PhantomData<(C, I)>);

impl<C, I> Cap<C, I> {
    /// The type-level capability anchor. (Tier-2 binds minting to a verified credential.)
    #[must_use]
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<C, I> Default for Cap<C, I> {
    fn default() -> Self {
        Self::new()
    }
}

/// The label-lattice flow relation: `Src: FlowsInto<Dst>` holds iff data at label `Src` may flow
/// to label `Dst`. Reflexive by the blanket impl below; users declare the lattice edges with
/// `impl FlowsInto<High> for Low {}`. An illegal flow is a trait-bound error (Tier-1 isolation).
pub trait FlowsInto<L> {}

/// Reflexivity: every label flows into itself.
impl<L> FlowsInto<L> for L {}

/// Compiles **only** when `Src: FlowsInto<Dst>`. The macro emits `const _: () =
/// assert_flows_into::<Src, Dst>();` for each `flow` axis, so an illegal flow becomes a
/// source-located trait-bound error checked at compile time. `const fn` so it can be the
/// initializer of an anonymous `const` item (no runtime cost, no user-body pollution).
pub const fn assert_flows_into<Src, Dst>()
where
    Src: FlowsInto<Dst>,
{
}

/// The failure envelope: a governed service declared `Faults<F>` tolerates up to `F` faults.
/// A const generic so the budget is part of the service's type (Tier-1); the Tier-2 guarantee
/// voids over budget (the `budgeted_guarantee_voids_over_budget` metatheorem).
pub struct Faults<const F: usize>;

/// Compile-time fault-budget check. `assert_tolerates::<F, G>()` compiles **only** when a service
/// that tolerates `F` faults is composed into a context requiring at least `G` (`F >= G`). An
/// over-budget composition — `F < G` — is a **compile error** (const-eval failure at
/// monomorphization). This makes budget-breach the third violation class (alongside admission and
/// isolation) checkable by `rustc`. Uses an inline `const` block (stable since 1.79) so the
/// comparison can reference the const-generic parameters.
pub const fn assert_tolerates<const F: usize, const G: usize>() {
    const {
        assert!(
            F >= G,
            "fault-budget breach: this service tolerates fewer faults than the required envelope"
        )
    }
}

/// Private runtime support for `#[dlc_d::agent_service]`-generated code. Re-exports exactly the
/// `dlc_core` items the macro's emitted admission certificate references, so a user crate needs
/// only depend on `dlc-d` (not on `dlc-core` directly). Not a stable API — do not use it.
#[doc(hidden)]
pub mod __rt {
    pub use dlc_core::decide::decide_pure;
    pub use dlc_core::judgment::{Ctx, TypingProblem};
    pub use dlc_core::syntax::{Prop, Term};
}

/// Example security labels for docs, tests, and the killer demo. Real services declare their own
/// labels and lattice edges; these ship a minimal two-point lattice (`Public ⊑ Secret`).
pub mod labels {
    /// The low / public confidentiality label.
    pub struct Public;
    /// The high / secret confidentiality label.
    pub struct Secret;

    // Public data may flow into a Secret context (confidentiality `⊑`); the reverse is absent,
    // so `assert_flows_into::<Secret, Public>()` is a compile error.
    impl super::FlowsInto<Secret> for Public {}
}

#[cfg(test)]
mod tests {
    use super::labels::{Public, Secret};
    use super::*;

    #[test]
    fn reflexive_and_declared_flows_typecheck() {
        assert_flows_into::<Public, Public>();
        assert_flows_into::<Secret, Secret>();
        assert_flows_into::<Public, Secret>();
    }

    #[test]
    fn capability_witness_constructs() {
        let _cap: Cap<Invoke<u8>, ()> = Cap::new();
        let _cap_default: Cap<Invoke<u8>, ()> = Cap::default();
    }

    #[test]
    fn fault_budget_is_a_type() {
        let _b: Faults<3> = Faults;
    }

    #[test]
    fn budget_tolerance_within_envelope_typechecks() {
        // A service tolerating F faults may serve a context requiring G ≤ F.
        assert_tolerates::<2, 1>();
        assert_tolerates::<1, 1>();
        assert_tolerates::<5, 0>();
        // (`assert_tolerates::<1, 2>()` would be a compile error — see tests/ui/over_budget.rs.)
    }
}
