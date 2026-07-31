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
//! **Step 3 + inc4:** the parsed envelope is *lowered* onto the governed `fn` — each present axis
//! emits an anonymous `const _` obligation referencing the `dlc_d` Tier-1 vocabulary, so
//! violations are ordinary `rustc` errors at the service definition: a missing capability witness
//! (E0061), an illegal `flow` (E0277), an over-budget composition (E0080), and — inc4 — a
//! demanded-vs-granted mismatch (`Issuer: Grants<Invoke<Tool>>` unsatisfied → E0277 spanned at the
//! tool name). The Tier-2 certificate is the same demanded-vs-granted fact posed to the VERIFIED
//! checker (`dlc_d::obligation::cap_problem` → `decide_pure`) as an emitted test, falsifiable on
//! any one-byte disagreement between envelope and `grants!` table. Emitted paths are `::dlc_d::…`,
//! so the annotated code must be in a crate that depends on `dlc-d` (the facade).

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
    let mut func = parse_macro_input!(item as ItemFn);
    // Tier-1 admission (cap-presence): append a capability-witness parameter, so every CALLER must
    // supply a `Cap<Invoke<Tool>, Issuer>` of the exact tool/issuer — a call without it, or with the
    // wrong capability, is a `rustc` type error. (`Cap::new()` is freely mintable: the witness type
    // proves only that the caller NAMED the demanded authority. Whether that authority was GRANTED
    // is the separate demanded-vs-granted gate — `assert_granted` at build, the checker-decided
    // certificate at test — and whether the credential is cryptographically VALID is
    // `runtime::admit`. A mint gated on the runtime credential is the U3 follow-up.)
    if let Some(cap) = &env.cap {
        let (tool, issuer) = (&cap.tool, &cap.issuer);
        let cap_param: syn::FnArg = syn::parse_quote! {
            _dlc_d_cap: ::dlc_d::Cap<::dlc_d::Invoke<#tool>, #issuer>
        };
        func.sig.inputs.push(cap_param);
    }
    let obligations = envelope::lower(&env);
    // If a `cap` axis is present, emit a hidden `#[test]` whose green run means the verified
    // checker accepted the admission certificate (macro out of the TCB — see `certificate_test`).
    let certificate = envelope::certificate_test(&env, &func.sig.ident);
    quote! {
        #obligations
        #certificate
        #func
    }
    .into()
}
