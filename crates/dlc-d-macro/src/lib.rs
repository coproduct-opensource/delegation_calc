//! `#[dlc_d::agent_service(...)]` — the R6.2 agent authority-envelope macro.
//!
//! This is an **untrusted** proc-macro (token manipulation). By design it is *out of the
//! trusted computing base*: soundness of "a green build is admission-safe" rides entirely on
//! the **verified certificate checker** (`dlc_core::decide` + the machine-checked
//! `rust_infer_sound`), never on this crate. A macro that emits a wrong certificate is
//! *rejected* by the verified checker, producing a compile error — so a green build is sound
//! regardless of macro correctness (spec/r6.2-agent-service-envelope.md §3.4).
//!
//! ## Envelope axes (spec §1–2)
//! ```ignore
//! #[dlc_d::agent_service(
//!     cap      = Invoke<Tool> @ issuer,   // admission control  (commit-I)
//!     flow     = chi <= l_low,            // cross-agent isolation (FlowsInto)
//!     budget   = Faults<f>,               // failure envelope
//!     delegate = attenuate_only,          // narrowing-only delegation
//! )]
//! ```
//!
//! ## Increment status
//! **Step 3 (this increment):** the parsed envelope is *lowered* onto the governed `fn` — each
//! present axis emits an anonymous `const _` obligation referencing the `dlc_d` Tier-1 vocabulary,
//! so violations are ordinary `rustc` errors at the service definition: an undefined capability
//! type, or an illegal `flow` (`Source: FlowsInto<Sink>` unsatisfied → trait-bound error). The
//! `fn` body is otherwise untouched. The Tier-2 certificate (a `dlc_core::TypingProblem` validated
//! by the verified checker) lands next. Emitted paths are `::dlc_d::…`, so the annotated code must
//! be in a crate that depends on `dlc-d` (the facade) — the normal entry point.

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

pub(crate) mod envelope;

/// The agent authority-envelope attribute macro. Applies to a `fn`; see the crate docs for the
/// axis grammar. Emits the parsed envelope's Tier-1 obligations as sibling `const _` items.
#[proc_macro_attribute]
pub fn agent_service(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse + validate the envelope axes; a malformed axis becomes a source-located `rustc`
    // diagnostic (via `parse_macro_input!`'s `compile_error!` emission) rather than silent UB.
    let env = parse_macro_input!(attr as envelope::Envelope);
    // The governed unit is a `fn`; a non-`fn` item is a clear parse error.
    let func = parse_macro_input!(item as ItemFn);
    let obligations = envelope::lower(&env);
    quote! {
        #obligations
        #func
    }
    .into()
}
