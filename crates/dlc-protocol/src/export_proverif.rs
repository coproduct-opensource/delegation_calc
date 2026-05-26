//! Export a DLC term to a ProVerif term.
//!
//! L2.2 cross-checks the Tamarin model by independently re-deriving the same
//! lemmas in ProVerif. This module produces the ProVerif input from the same
//! Rust source as Tamarin export.

/// Render a `Term` as ProVerif term syntax.
pub fn term_to_proverif(_term: &dlc_core::syntax::Term) -> String {
    String::new()
}
