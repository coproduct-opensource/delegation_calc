//! DLC reference proof checker.
//!
//! CI gates this crate at **< 2000 LOC total** (measured by `tokei`) — the
//! marketing claim "a ~2000-line Rust program compiled to WASM" must be true
//! at every commit. See `scripts/check-loc-budget.sh`.

#![forbid(unsafe_code)]

pub mod check;
pub mod replay;

/// Outcome of a verification call.
#[derive(Debug)]
pub enum VerifyResult {
    /// The proof checks under both the logical and cryptographic judgments.
    Ok,
    /// The proof failed; the byte offset of the offending subterm is returned
    /// to aid debugging without leaking unrelated state.
    Fail { offset: usize, reason: String },
}
