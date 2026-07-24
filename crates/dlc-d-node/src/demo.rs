//! The demo workload — shared by the binary and the tests.
//!
//! Two properties of these commands are deliberate, not incidental:
//!
//! * **Every term is CLOSED.** The R2 transport theorems carry `ClosedTm`
//!   premises on stores (`hstores`) and on log payloads (`hlog`); running the
//!   node on an open term like `var 0` would put the demo outside the hypotheses
//!   of the very theorems it is meant to deploy. The initial store is the closed
//!   identity `λ_:atom0. x`, and both commands map closed stores to closed
//!   stores.
//! * **The store genuinely changes, and the order matters.** `[dup, dup, fst]`
//!   takes `id ↦ ⟨id,id⟩ ↦ ⟨⟨id,id⟩,⟨id,id⟩⟩ ↦ ⟨id,id⟩`: the final store differs
//!   from the initial one (so convergence is not observed over a no-op — the
//!   `RsmAntiVacuity` discipline), and permuting the log gives a different
//!   result (so the total order the consensus layer provides is load-bearing).

use dlc_core::rsm::Command;
use dlc_core::syntax::{Prop, Term};

/// The closed initial store: the identity `λ_:atom0. x`.
pub fn init() -> Term {
    Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)))
}

/// `dup` — `λ_:atom0. ⟨x, x⟩`, the anti-vacuity command mirroring
/// `DLCD.RsmAntiVacuity.dup`: applied to a store `s` it reduces to `⟨s, s⟩`, a
/// genuinely different head constructor.
pub fn dup() -> Command {
    Command {
        payload: Term::Lam(
            Box::new(Prop::Atom(0)),
            Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
        ),
        cap: None,
    }
}

/// `fst` — `λ_:atom0. π₁ x`: projects a paired store back to its left component.
/// Included so the workload is not monotone growth and so log ORDER is
/// observable in the final store.
pub fn fst() -> Command {
    Command {
        payload: Term::Lam(
            Box::new(Prop::Atom(0)),
            Box::new(Term::Fst(Box::new(Term::Var(0)))),
        ),
        cap: None,
    }
}

/// `dup` carrying a (Phase-1.0-opaque) capability slot. The node CARRIES `cap`
/// and never checks it — authorization is a `Prop`-layer obligation
/// (`rust_capability_safety` is conditioned on `Authorized` of the decoded
/// command) and R6.2's surface is what discharges it at compile time.
pub fn dup_with_cap() -> Command {
    Command {
        payload: dup().payload,
        cap: Some(Prop::Atom(7)),
    }
}

/// The demo workload: `[dup, dup, fst]`.
pub fn workload() -> Vec<Command> {
    vec![dup_with_cap(), dup(), fst()]
}
