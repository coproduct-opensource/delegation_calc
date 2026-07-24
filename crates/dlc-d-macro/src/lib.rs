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
//! **Step 2 (this increment):** the four envelope axes are parsed into [`envelope::Envelope`]
//! with a hand `syn::Parse` over the non-standard grammar (`@`, `<=`), producing source-located
//! diagnostics on malformed axes. The annotated item is still passed through unchanged; Tier-1
//! phantom-type emission and the Tier-2 certificate land next.

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Item};

pub(crate) mod envelope;

/// The agent authority-envelope attribute macro. See the crate docs for the axis grammar.
#[proc_macro_attribute]
pub fn agent_service(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse + validate the envelope axes; a malformed axis becomes a source-located `rustc`
    // diagnostic (via `parse_macro_input!`'s `compile_error!` emission) rather than silent UB.
    let _envelope = parse_macro_input!(attr as envelope::Envelope);
    // Validate the annotated item is a well-formed Rust item.
    let item = parse_macro_input!(item as Item);
    // SCAFFOLD: emit unchanged. Tier-1 phantom types + Tier-2 certificate consume `_envelope` next.
    quote! { #item }.into()
}
