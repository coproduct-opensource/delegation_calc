//! The verifier entry point.
//!
//! Takes a wire-format proof term, a claimed proposition, and a keyring. Runs
//! both `decide_pure` from `dlc-core` (T1's algorithm) and the cryptographic
//! checks from `dlc-crypto` at every `says` node. Returns `Ok` iff both judgment
//! forms succeed — this is what T2 says they coincide.

use dlc_core::judgment::KeyRing;
use dlc_core::syntax::Prop;

use crate::VerifyResult;

/// Verify a wire-format proof of `claimed` under `keyring`.
pub fn verify(_wire: &[u8], _claimed: &Prop, _keyring: &KeyRing) -> VerifyResult {
    VerifyResult::Fail {
        offset: 0,
        reason: "verifier not implemented".into(),
    }
}
