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
//! **Step 1 (this scaffold):** the attribute is recognized, the annotated item is validated
//! (it must parse as a Rust item) and passed through unchanged. Tier-1 phantom-type emission
//! (`Cap`/`FlowsInto`/`Faults`) and the Tier-2 certificate (a `dlc_core::TypingProblem`
//! validated at build time by the verified checker) land in subsequent increments.

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Item};

/// The agent authority-envelope attribute macro. See the crate docs for the axis grammar.
#[proc_macro_attribute]
pub fn agent_service(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // Validate the annotated item is a well-formed Rust item; a parse failure becomes a
    // source-located `rustc` diagnostic rather than a silent miscompile.
    let item = parse_macro_input!(item as Item);
    // SCAFFOLD: emit unchanged. Envelope parsing + Tier-1 types + Tier-2 certificate next.
    quote! { #item }.into()
}
