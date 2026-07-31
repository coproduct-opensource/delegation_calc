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

/// Runtime admission — the verify-then-authorize PEP that gives a compile-time [`Cap`] its VALIDITY
/// (real Ed25519 credential check bound to the tool). See [`runtime::admit`].
pub mod runtime;

/// The host-facing admission surface: a PEP-shaped [`Decision`](admission::Decision) over
/// [`runtime::admit`], for embedding DLC-D admission in a host reference monitor
/// (`nucleus`/`portcullis-core`). See `spec/nucleus-admission-integration.md`.
pub mod admission;

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

/// The grant relation: `I: Grants<C>` holds iff issuer `I` has declared the capability `C` in the
/// crate's [`grants!`] table. The `#[agent_service]` macro emits
/// `assert_granted::<Issuer, Invoke<Tool>>()` for each `cap` axis, so demanding a capability the
/// issuer never granted is a source-located trait-bound error at `cargo build` — the
/// demanded-vs-granted admission gate. The same demanded-vs-granted fact is decided by the
/// VERIFIED checker in the emitted certificate test ([`obligation::cap_problem`]).
#[diagnostic::on_unimplemented(
    message = "unauthorized tool: issuer `{Self}` has not granted the capability `{C}`",
    label = "this envelope demands a capability its issuer never granted",
    note = "declare the grant with `dlc_d::grants! {{ Issuer: Tool }}`; the demanded-vs-granted obligation is re-decided by the verified checker (`decide_pure`) in the emitted certificate test"
)]
pub trait Grants<C> {}

/// Compiles **only** when `I: Grants<C>` — the build-time demanded-vs-granted admission gate.
/// `const fn` so it can anchor an anonymous `const` item (no runtime cost).
pub const fn assert_granted<I, C>()
where
    I: Grants<C>,
{
}

/// Declare the crate's capability grants: which issuer granted which tools.
///
/// ```ignore
/// dlc_d::grants! { Admin: FileWrite, NetRead; Ops: SendEmail }
/// ```
///
/// Expands to (1) `impl Grants<Invoke<Tool>> for Issuer` for each pair — the build-time gate the
/// `cap` axis checks — and (2) the `__DLC_D_GRANTS` name table the emitted certificate test feeds
/// to the verified checker. The two lowerings come from the SAME declaration, so they cannot
/// disagree with each other; they can disagree with an envelope, which is exactly the misconfiguration
/// the gates exist to catch. Invoke at crate root (the certificate test resolves
/// `crate::__DLC_D_GRANTS`).
#[macro_export]
macro_rules! grants {
    ( $( $issuer:ident : $( $tool:ident ),+ );* $(;)? ) => {
        $( $( impl $crate::Grants<$crate::Invoke<$tool>> for $issuer {} )+ )*
        #[doc(hidden)]
        #[allow(dead_code)]
        pub const __DLC_D_GRANTS: &[(&str, &str)] =
            &[ $( $( (stringify!($issuer), stringify!($tool)), )+ )* ];
    };
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

/// The Tier-2 admission obligation: demanded-vs-granted, decided by the verified checker.
pub mod obligation {
    use dlc_core::judgment::{Ctx, TypingProblem};
    use dlc_core::principal::{Principal, PrincipalId};
    use dlc_core::syntax::{Prop, Term};

    /// A deterministic (non-cryptographic) principal for an issuer NAME: 32 id bytes expanded from
    /// the FNV-1a hash of the name. Distinct issuer names get distinct principals, so a grant row
    /// for the wrong issuer cannot discharge a demand. Identity *binding* (this name really is this
    /// key) is [`runtime::admit`](crate::runtime::admit)'s job, not this function's.
    pub fn issuer_principal(issuer: &str) -> Principal {
        let mut h: u32 = 0x811c_9dc5;
        for b in issuer.bytes() {
            h ^= u32::from(b);
            h = h.wrapping_mul(0x0100_0193);
        }
        let mut id = [0u8; 32];
        for (i, chunk) in id.chunks_mut(4).enumerate() {
            let hi = (h ^ (i as u32)).wrapping_mul(0x0100_0193);
            chunk.copy_from_slice(&hi.to_le_bytes());
        }
        Principal::Atom(PrincipalId(id))
    }

    /// Build the demanded-vs-granted admission problem for one `cap` axis.
    ///
    /// The GOAL is the envelope's demand: `issuer says Atom(cap_atom(tool))`. The CONTEXT presents
    /// the issuer's declared credential from the [`grants!`](crate::grants) table: the matching
    /// grant if declared, else the issuer's first grant (a credential that cannot discharge this
    /// demand), else nothing (an unbound `Var 0`, which the checker rejects). The term is `Var 0` —
    /// fragment F, covered by `rust_infer_sound`.
    ///
    /// `decide_pure` on the result is therefore TRUE iff the grants table contains this
    /// (issuer, tool) pair — a non-constant function of two independently declared facts. Perturb
    /// either declaration by one byte and the verified checker goes RED
    /// (`tests/certificate.rs::cap_obligation_*`).
    pub fn cap_problem(grants: &[(&str, &str)], issuer: &str, tool: &str) -> TypingProblem {
        let demanded = Prop::Says(
            issuer_principal(issuer),
            Box::new(Prop::Atom(crate::runtime::cap_atom(tool))),
        );
        let presented = grants
            .iter()
            .find(|(i, t)| *i == issuer && *t == tool)
            .or_else(|| grants.iter().find(|(i, _)| *i == issuer));
        let ctx = match presented {
            Some((gi, gt)) => Ctx::empty().cons_a(Prop::Says(
                issuer_principal(gi),
                Box::new(Prop::Atom(crate::runtime::cap_atom(gt))),
            )),
            None => Ctx::empty(),
        };
        TypingProblem {
            ctx,
            term: Term::Var(0),
            prop: demanded,
        }
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
