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

/// A tool a governed service may invoke. `NAME` is the tool's **stable credential name** — the
/// string every layer keys on: the `grants!` table, the emitted certificate's cap atom, and the
/// runtime credential message ([`runtime::cap_atom`]`(NAME)`). Deriving decouples credential
/// identity from the Rust identifier: `#[derive(Tool)]` defaults `NAME` to the type's ident, and
/// `#[tool(name = "send-email")]` pins it so renaming the struct cannot silently invalidate
/// issued credentials.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a dlc_d tool: it has no stable credential name",
    label = "expected a type deriving `dlc_d::Tool`",
    note = "add `#[derive(dlc_d::Tool)]` (optionally `#[tool(name = \"stable-name\")]`) to the tool type"
)]
pub trait Tool {
    /// The stable credential name (defaults to the type ident under `#[derive(Tool)]`).
    const NAME: &'static str;
}

/// Derive [`Tool`] for a unit struct; `#[tool(name = "…")]` overrides the default (the ident).
pub use dlc_d_macro::Tool;

/// The "invoke this tool" capability kind — the `C` in `Cap<C, I>`.
pub struct Invoke<T>(PhantomData<T>);

/// A capability witness: a value of `Cap<Invoke<Tool>, Issuer>` in scope proves the holder
/// presented authority for `Invoke<Tool>` from `Issuer`. The macro requires such a witness at
/// each governed write; its **absence** is a `rustc` type error (Tier-1 admission control).
///
/// Two mints exist, and the difference IS the U3 guarantee:
/// - [`Cap::admit`] — the **gated** mint: succeeds only for a genuine issuer-signed Ed25519
///   credential over this tool's cap atom (via [`runtime::admit`]). A `Cap` from this path
///   carries runtime validity.
/// - [`Cap::unchecked`] — the free mint, for tests/bootstrap/examples ONLY. It proves the
///   caller *named* the authority, nothing more.
pub struct Cap<C, I>(PhantomData<(C, I)>);

impl<T: Tool, I> Cap<Invoke<T>, I> {
    /// **The gated mint (U3).** Verify an issuer-signed credential for exactly this tool —
    /// a real Ed25519 [`runtime::admit`] over `cap_atom(T::NAME)`, fail-closed — and mint the
    /// typed witness only on success. The atom the credential must be signed over is the SAME
    /// `cap_atom(T::NAME)` the emitted certificate demands, by construction (one function, one
    /// name): the compile-time and runtime verdicts are about the same fact.
    ///
    /// # Errors
    /// [`runtime::AdmitError::Unauthorized`] if the signature does not verify for this tool.
    pub fn admit(
        keyring: &dlc_core::judgment::KeyRing,
        issuer: &dlc_core::principal::Principal,
        sig: &dlc_core::syntax::Signature,
    ) -> Result<Self, runtime::AdmitError> {
        runtime::admit(keyring, issuer, T::NAME, sig)?;
        Ok(Self(PhantomData))
    }
}

impl<C, I> Cap<C, I> {
    /// The **free** mint: a type-level anchor with no runtime validity. Tests, bootstrap, and
    /// examples only — production call sites should obtain their witness via [`Cap::admit`].
    #[must_use]
    pub const fn unchecked() -> Self {
        Self(PhantomData)
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

/// The runtime-readable grant list of one issuer, produced by [`grants!`]. Type-routed (an
/// associated const, not a crate-root item), so `grants!` may be invoked in any module and the
/// emitted certificate finds the table through the issuer type. Names come from
/// [`Tool::NAME`], so a `#[tool(name = "…")]` stable name flows into the checker obligation.
#[diagnostic::on_unimplemented(
    message = "no `dlc_d::grants!` declaration covers issuer `{Self}`",
    label = "this envelope's issuer has no declared grants",
    note = "declare the issuer's grants with `dlc_d::grants! {{ Issuer: Tool, … }}`"
)]
pub trait IssuerGrants {
    /// The stable credential names ([`Tool::NAME`]) this issuer has granted.
    const GRANTS: &'static [&'static str];
}

/// Declare capability grants: which issuer granted which tools.
///
/// ```ignore
/// dlc_d::grants! { Admin: FileWrite, NetRead; Ops: SendEmail }
/// ```
///
/// Expands, per issuer, to (1) `impl Grants<Invoke<Tool>> for Issuer` for each granted tool —
/// the build-time gate the `cap` axis checks — and (2) an [`IssuerGrants`] impl carrying the
/// granted [`Tool::NAME`] list the emitted certificate test feeds to the verified checker. The
/// two lowerings come from the SAME declaration, so they cannot disagree with each other; they
/// can disagree with an envelope, which is exactly the misconfiguration the gates catch. Tools
/// must derive [`Tool`]. May be invoked in any module; list each issuer once (a second
/// `grants!` for the same issuer is a duplicate-impl error, by design).
#[macro_export]
macro_rules! grants {
    ( $( $issuer:ty : $( $tool:ty ),+ );* $(;)? ) => {
        $(
            $( impl $crate::Grants<$crate::Invoke<$tool>> for $issuer {} )+
            impl $crate::IssuerGrants for $issuer {
                const GRANTS: &'static [&'static str] =
                    &[ $( <$tool as $crate::Tool>::NAME ),+ ];
            }
        )*
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
    /// The GOAL is the envelope's demand: `issuer says Atom(cap_atom(tool))`. The CONTEXT
    /// presents the issuer's declared credential from its [`IssuerGrants::GRANTS`](crate::IssuerGrants)
    /// list: the matching grant if declared, else the issuer's first grant (a credential that
    /// cannot discharge this demand), else nothing (an unbound `Var 0`, which the checker
    /// rejects — an issuer with no grants fails closed). The term is `Var 0` — fragment F,
    /// covered by `rust_infer_sound`.
    ///
    /// `decide_pure` on the result is therefore TRUE iff `granted` contains `tool` — a
    /// non-constant function of two independently declared facts (envelope demand vs `grants!`
    /// declaration). Perturb either by one byte and the verified checker goes RED
    /// (`tests/certificate.rs::cap_obligation_*`).
    pub fn cap_problem(granted: &[&str], issuer: &str, tool: &str) -> TypingProblem {
        let demanded = Prop::Says(
            issuer_principal(issuer),
            Box::new(Prop::Atom(crate::runtime::cap_atom(tool))),
        );
        let presented = if granted.contains(&tool) {
            Some(tool)
        } else {
            granted.first().copied()
        };
        let ctx = match presented {
            Some(g) => Ctx::empty().cons_a(Prop::Says(
                issuer_principal(issuer),
                Box::new(Prop::Atom(crate::runtime::cap_atom(g))),
            )),
            None => Ctx::empty(),
        };
        TypingProblem {
            ctx,
            term: Term::Var(0),
            prop: demanded,
        }
    }

    /// U3 divergence guard: the atom the certificate GOAL demands and the atom the runtime
    /// credential must be signed over are the same value for the same name. Today this holds
    /// because both sides call the one [`runtime::cap_atom`](crate::runtime::cap_atom) — this
    /// extractor lets a test re-check the emitted problem itself, so a future re-duplication of
    /// the hash (the pre-inc4 state) is caught by a RED, not a code review.
    pub fn demanded_atom(problem: &TypingProblem) -> Option<u32> {
        match &problem.prop {
            Prop::Says(_, inner) => match **inner {
                Prop::Atom(a) => Some(a),
                _ => None,
            },
            _ => None,
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
    fn capability_witness_constructs_unchecked() {
        // The FREE mint — named for what it is; the gated mint is Cap::admit (runtime tests).
        let _cap: Cap<Invoke<u8>, ()> = Cap::unchecked();
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
