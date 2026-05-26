//! Replay verification against a recorded trace.
//!
//! Used by the §4.4 protocol-logic correspondence to confirm that a Tamarin
//! trace projects to a DLC proof which this verifier accepts.

use crate::VerifyResult;

/// Replay a recorded trace, returning the first failure or `Ok`.
pub fn replay(_trace: &[u8]) -> VerifyResult {
    VerifyResult::Fail {
        offset: 0,
        reason: "replay not implemented".into(),
    }
}
