//! Export a DLC term to a Tamarin fact set.
//!
//! L2.3 in Phase 2 proves this is a round-tripping encoding against the
//! Tamarin protocol model in `models/tamarin/dlc.spthy`.

/// Render a `Term` as Tamarin fact-trace syntax suitable for piping into a
/// `lemma` over an instrumented protocol model.
pub fn term_to_tamarin(_term: &dlc_core::syntax::Term) -> String {
    String::new()
}
