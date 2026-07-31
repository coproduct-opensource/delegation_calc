//! The `#[agent_service(...)]` envelope grammar and its parser.
//!
//! The axis grammar uses tokens that are not valid Rust *syntax* (`Invoke<Tool> @ issuer`,
//! `chi <= l_low`) though they are valid Rust *tokens*, so we hand-write a [`syn::parse::Parse`]
//! over the raw `ParseStream` rather than reusing `syn::Meta`. Each axis records its spans so the
//! later Tier-1/Tier-2 lowering can point diagnostics at the offending source.

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{Ident, LitInt, Token};

/// Last-segment ident of a path — the token that names the thing for humans (`tools::Send` →
/// `Send`). Used for diagnostics spans and the issuer's display name.
fn tail(p: &syn::Path) -> &Ident {
    &p.segments
        .last()
        .expect("syn::Path always has ≥1 segment")
        .ident
}

/// Clone a path with every segment respanned — lands a diagnostic's caret on `span`'s token.
fn respan(p: &syn::Path, span: Span) -> syn::Path {
    let mut p = p.clone();
    for seg in p.segments.iter_mut() {
        seg.ident.set_span(span);
    }
    p
}

mod kw {
    syn::custom_keyword!(cap);
    syn::custom_keyword!(flow);
    syn::custom_keyword!(budget);
    syn::custom_keyword!(delegate);
    syn::custom_keyword!(Invoke);
    syn::custom_keyword!(Faults);
    syn::custom_keyword!(attenuate_only);
}

// Axis fields are read by the tests and will be consumed by the Tier-1 phantom-type and
// Tier-2 certificate lowering (next increments); allow them to be write-only until then.

/// `cap = Invoke<Tool> @ issuer` — the admission-control capability (commit-I). Tool and issuer
/// are full paths (`Invoke<tools::Send> @ auth::Ops`), so namespaced vocab needs no `use`.
#[derive(Clone)]
#[allow(dead_code)]
pub struct CapAxis {
    pub tool: syn::Path,
    pub issuer: syn::Path,
}

/// `flow = chi <= l_low` — the cross-agent isolation flow constraint (`FlowsInto`).
#[derive(Clone)]
#[allow(dead_code)]
pub struct FlowAxis {
    pub source: syn::Path,
    pub sink: syn::Path,
}

/// `budget = Faults<f>` — the failure envelope (tolerated fault count).
#[derive(Clone)]
#[allow(dead_code)]
pub struct BudgetAxis {
    pub faults: LitInt,
}

/// `delegate = attenuate_only` — narrowing-only delegation.
#[derive(Clone)]
#[allow(dead_code)]
pub struct DelegateAxis {
    pub span: Span,
}

/// The parsed `#[agent_service(...)]` envelope. All axes are optional; a bare
/// `#[agent_service]` yields an all-`None` envelope.
#[derive(Clone, Default)]
pub struct Envelope {
    pub cap: Option<CapAxis>,
    pub flow: Option<FlowAxis>,
    pub budget: Option<BudgetAxis>,
    pub delegate: Option<DelegateAxis>,
}

impl Parse for Envelope {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut env = Envelope::default();
        while !input.is_empty() {
            let lookahead = input.lookahead1();
            if lookahead.peek(kw::cap) {
                let key: kw::cap = input.parse()?;
                input.parse::<Token![=]>()?;
                input.parse::<kw::Invoke>()?;
                input.parse::<Token![<]>()?;
                let tool: syn::Path = input.parse()?;
                input.parse::<Token![>]>()?;
                input.parse::<Token![@]>()?;
                let issuer: syn::Path = input.parse()?;
                if env.cap.replace(CapAxis { tool, issuer }).is_some() {
                    return Err(syn::Error::new(key.span, "duplicate `cap` axis"));
                }
            } else if lookahead.peek(kw::flow) {
                let key: kw::flow = input.parse()?;
                input.parse::<Token![=]>()?;
                let source: syn::Path = input.parse()?;
                input.parse::<Token![<=]>()?;
                let sink: syn::Path = input.parse()?;
                if env.flow.replace(FlowAxis { source, sink }).is_some() {
                    return Err(syn::Error::new(key.span, "duplicate `flow` axis"));
                }
            } else if lookahead.peek(kw::budget) {
                let key: kw::budget = input.parse()?;
                input.parse::<Token![=]>()?;
                input.parse::<kw::Faults>()?;
                input.parse::<Token![<]>()?;
                let faults: LitInt = input.parse()?;
                // Validate the fault count is a plain unsuffixed integer.
                faults.base10_parse::<u32>()?;
                input.parse::<Token![>]>()?;
                if env.budget.replace(BudgetAxis { faults }).is_some() {
                    return Err(syn::Error::new(key.span, "duplicate `budget` axis"));
                }
            } else if lookahead.peek(kw::delegate) {
                let key: kw::delegate = input.parse()?;
                input.parse::<Token![=]>()?;
                let d: kw::attenuate_only = input.parse()?;
                if env
                    .delegate
                    .replace(DelegateAxis { span: d.span })
                    .is_some()
                {
                    return Err(syn::Error::new(key.span, "duplicate `delegate` axis"));
                }
            } else {
                return Err(lookahead.error());
            }
            // Optional separating comma (also permits a trailing comma).
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            } else if !input.is_empty() {
                return Err(input.error("expected `,` between envelope axes"));
            }
        }
        Ok(env)
    }
}

/// Lower a parsed [`Envelope`] onto its governed `fn` as sibling anonymous `const _` obligations
/// referencing the `dlc_d` Tier-1 vocabulary. Only present axes emit anything, so a bare
/// `#[agent_service]` lowers to nothing. Emitted at the service's span so violations are
/// source-located `rustc` errors.
pub fn lower(env: &Envelope) -> TokenStream {
    let mut out = TokenStream::new();

    // The `cap` axis is enforced twice: an injected capability-witness parameter (see
    // `agent_service`) makes a *missing* witness a call-site error, and the demanded-vs-granted
    // gate below makes demanding a tool the issuer never granted a build error. Spanned at the
    // tool ident so the E0277 caret lands on the offending tool name.
    if let Some(cap) = &env.cap {
        let tool = &cap.tool;
        let tool_span = tail(tool).span();
        // Re-span the issuer path onto the tool token: interpolated paths keep their own spans,
        // and rustc anchors the E0277 caret on the `I` type argument — respanning lands the caret
        // on the demanded tool name, the token the developer has to change
        // (tests/ui/unauthorized_tool.stderr pins this).
        let issuer = respan(&cap.issuer, tool_span);
        out.extend(quote::quote_spanned! {tool_span=>
            const _: () = ::dlc_d::assert_granted::<#issuer, ::dlc_d::Invoke<#tool>>();
        });
    }

    if let Some(flow) = &env.flow {
        let (source, sink) = (&flow.source, &flow.sink);
        // Tier-1 isolation: `source ⊑ sink` in the label lattice; an illegal flow is a
        // trait-bound error (`Source: FlowsInto<Sink>` unsatisfied).
        out.extend(quote! {
            const _: () = ::dlc_d::assert_flows_into::<#source, #sink>();
        });
    }

    if let Some(budget) = &env.budget {
        let faults = &budget.faults;
        // Tier-1 budget: anchor the fault envelope as a type.
        out.extend(quote! {
            const _: ::dlc_d::Faults<#faults> = ::dlc_d::Faults;
        });
    }

    out
}

/// If the envelope carries a `cap` axis, emit a hidden `#[test]` that constructs the
/// demanded-vs-granted admission obligation (`dlc_d::obligation::cap_problem`: the envelope's
/// demanded `issuer says Atom(cap_atom(tool))` against the credential the crate's `grants!` table
/// actually declares) and asserts the VERIFIED checker (`dlc_core::decide::decide_pure`) accepts
/// it. The problem is a non-constant function of two independently declared facts — envelope and
/// grant table — so a misconfigured envelope goes RED at the checker, and a green `cargo test`
/// means, by the machine-checked `rust_infer_sound`, a real `Deriv` exists. The macro stays out of
/// the TCB: it only *poses* the problem; the verified kernel decides it.
///
/// (Fence: a macro that emits NOTHING is not caught by the checker — omission is guarded by the
/// golden-obligation tests in `dlc-d/tests/certificate.rs`, not by this emission. The build-time
/// gate for the same fact is the `assert_granted` const in `lower`; the checker-decided form runs
/// at `cargo test` time because `decide_pure` needs heap types the const layer cannot evaluate.)
pub fn certificate_test(env: &Envelope, fn_ident: &Ident) -> TokenStream {
    let Some(cap) = &env.cap else {
        return TokenStream::new();
    };
    let (tool, issuer) = (&cap.tool, &cap.issuer);
    // The issuer's display/principal name is its type name (last path segment); the TOOL's name
    // is `Tool::NAME` — the stable credential name — so a `#[tool(name = "…")]` override flows
    // into the checker obligation, not the Rust ident.
    let issuer_name = tail(issuer).to_string();
    let test_name = quote::format_ident!("__dlc_d_cert_{}", fn_ident);
    quote! {
        // `#[cfg(test)]` so the certificate is validated at `cargo test` time and excluded from
        // normal/example/release builds (no dead-code warning, not shipped).
        #[cfg(test)]
        #[test]
        #[allow(non_snake_case)]
        fn #test_name() {
            let __problem = ::dlc_d::obligation::cap_problem(
                <#issuer as ::dlc_d::IssuerGrants>::GRANTS,
                #issuer_name,
                <#tool as ::dlc_d::Tool>::NAME,
            );
            assert!(
                ::dlc_d::__rt::decide_pure(&__problem),
                "dlc_d::agent_service: the demanded capability `{}` @ `{}` is not discharged \
                 by the issuer's `grants!` declaration (rejected by the verified checker)",
                <#tool as ::dlc_d::Tool>::NAME,
                #issuer_name,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_full_envelope() {
        let env: Envelope = syn::parse_str(
            "cap = Invoke<FileWrite> @ admin, flow = secret <= public, \
                            budget = Faults<1>, delegate = attenuate_only",
        )
        .expect("well-formed envelope should parse");
        let cap = env.cap.expect("cap present");
        assert_eq!(tail(&cap.tool).to_string(), "FileWrite");
        assert_eq!(tail(&cap.issuer).to_string(), "admin");
        let flow = env.flow.expect("flow present");
        assert_eq!(tail(&flow.source).to_string(), "secret");
        assert_eq!(tail(&flow.sink).to_string(), "public");
        assert_eq!(
            env.budget
                .expect("budget present")
                .faults
                .base10_parse::<u32>()
                .unwrap(),
            1
        );
        assert!(env.delegate.is_some());
    }

    #[test]
    fn bare_envelope_is_empty() {
        let env: Envelope = syn::parse_str("").expect("empty envelope parses");
        assert!(env.cap.is_none() && env.flow.is_none() && env.budget.is_none());
    }

    #[test]
    fn rejects_unknown_axis() {
        assert!(syn::parse_str::<Envelope>("nonsense = 3").is_err());
    }

    #[test]
    fn rejects_malformed_budget() {
        assert!(syn::parse_str::<Envelope>("budget = NotAFault").is_err());
    }

    #[test]
    fn rejects_malformed_cap() {
        // Missing the `@ issuer`.
        assert!(syn::parse_str::<Envelope>("cap = Invoke<Tool>").is_err());
    }

    #[test]
    fn accepts_namespaced_paths() {
        // Real crates namespace their vocab — no forced `use` imports.
        let env: Envelope = syn::parse_str(
            "cap = Invoke<tools::Send> @ auth::Ops, flow = labels::Lo <= labels::Hi",
        )
        .expect("path-qualified envelope should parse");
        let cap = env.cap.expect("cap present");
        assert_eq!(tail(&cap.tool).to_string(), "Send");
        assert_eq!(tail(&cap.issuer).to_string(), "Ops");
        assert_eq!(tail(&env.flow.expect("flow").sink).to_string(), "Hi");
    }
}
