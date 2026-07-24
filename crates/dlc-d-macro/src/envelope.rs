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

/// `cap = Invoke<Tool> @ issuer` — the admission-control capability (commit-I).
#[derive(Clone)]
#[allow(dead_code)]
pub struct CapAxis {
    pub tool: Ident,
    pub issuer: Ident,
}

/// `flow = chi <= l_low` — the cross-agent isolation flow constraint (`FlowsInto`).
#[derive(Clone)]
#[allow(dead_code)]
pub struct FlowAxis {
    pub source: Ident,
    pub sink: Ident,
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
                let tool: Ident = input.parse()?;
                input.parse::<Token![>]>()?;
                input.parse::<Token![@]>()?;
                let issuer: Ident = input.parse()?;
                if env.cap.replace(CapAxis { tool, issuer }).is_some() {
                    return Err(syn::Error::new(key.span, "duplicate `cap` axis"));
                }
            } else if lookahead.peek(kw::flow) {
                let key: kw::flow = input.parse()?;
                input.parse::<Token![=]>()?;
                let source: Ident = input.parse()?;
                input.parse::<Token![<=]>()?;
                let sink: Ident = input.parse()?;
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

    if let Some(cap) = &env.cap {
        let (tool, issuer) = (&cap.tool, &cap.issuer);
        // Tier-1 admission: anchor the capability types `Invoke<Tool> @ Issuer`. An undefined
        // `Tool`/`Issuer` type is a compile error here. (Presence-of-witness enforcement — a
        // missing `Cap` value at the write site — is a later increment; this pins the types.)
        out.extend(quote! {
            const _: ::core::marker::PhantomData<
                ::dlc_d::Cap<::dlc_d::Invoke<#tool>, #issuer>,
            > = ::core::marker::PhantomData;
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
        assert_eq!(cap.tool.to_string(), "FileWrite");
        assert_eq!(cap.issuer.to_string(), "admin");
        let flow = env.flow.expect("flow present");
        assert_eq!(flow.source.to_string(), "secret");
        assert_eq!(flow.sink.to_string(), "public");
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
}
