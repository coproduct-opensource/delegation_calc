//! DLC wire format and protocol-correspondence exporters.
//!
//! The wire format is a content-addressed Merkle DAG, serialized as
//! COSE_Sign1-wrapped CBOR. This crate also owns the round-trip encoders to
//! Tamarin (`models/tamarin/dlc.spthy` facts) and ProVerif terms, used by the
//! L2.3 lemma in Phase 2.

#![forbid(unsafe_code)]

pub mod envelope;
pub mod export_proverif;
pub mod export_tamarin;
// `grade_quantale` (the DP-budget Quantale) depends on the PRIVATE `coproduct-algebra`
// and lives in the workspace-excluded `dlc-grade-quantale` crate so the public build
// never resolves that path (a feature-gate is insufficient — cargo still loads an
// optional path dep's manifest).
pub mod wire;

/// Errors during wire encoding / decoding.
#[derive(Debug, thiserror::Error)]
pub enum ProtocolError {
    /// CBOR malformed.
    #[error("cbor decode error: {0}")]
    Cbor(String),
    /// COSE envelope malformed.
    #[error("cose decode error: {0}")]
    Cose(String),
}
