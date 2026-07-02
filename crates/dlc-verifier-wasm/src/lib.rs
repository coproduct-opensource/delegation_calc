//! wasm32 wrapper for the DLC verifier.
//!
//! Exposes one entry point, [`verify`], suitable for invocation from
//! JavaScript via the `wasm-bindgen` generated glue. The function takes
//! three byte slices and returns `1` on successful verification, `0`
//! otherwise.
//!
//! The richer return shape (per-node typing errors, IFC-label diagnostics,
//! offending principal index) lands at M3.M21 alongside the full
//! `dlc-verifier` rewrite. This module is intentionally minimal so the
//! `wasm-bindgen` interface is stable from day one.

#![forbid(unsafe_code)]

use wasm_bindgen::prelude::*;

/// Verify a DLC token against a claimed type and keyring.
///
/// # Arguments
/// * `wire` — CBOR-encoded DLC token (`dlc-protocol::wire::encode`).
/// * `claimed` — CBOR-encoded `Prop` the caller claims `wire` proves
///   (`wire::encode_prop`).
/// * `keyring` — CBOR-encoded keyring (`wire::encode_keyring`).
///
/// # Returns
/// `1` if verification succeeds, `0` otherwise (including on malformed
/// inputs). The richer shape (error kind, offending subterm) is the
/// M3.M21 wire-up.
#[wasm_bindgen]
pub fn verify(wire: &[u8], claimed: &[u8], keyring: &[u8]) -> u32 {
    verify_raw(wire, claimed, keyring)
}

/// Native-target equivalent of [`verify`]. Kept as a `pub fn` so the
/// `rlib` target builds on non-wasm hosts (used by the dlc-verifier test
/// harness and by `dlc-bench` for the complexity regression).
pub fn verify_raw(wire: &[u8], claimed: &[u8], keyring: &[u8]) -> u32 {
    let Ok(claimed) = dlc_protocol::wire::decode_prop(claimed) else {
        return 0;
    };
    let Ok(keyring) = dlc_protocol::wire::decode_keyring(keyring) else {
        return 0;
    };
    match dlc_verifier::check::verify(wire, &claimed, &keyring) {
        dlc_verifier::VerifyResult::Ok => 1,
        dlc_verifier::VerifyResult::Fail { .. } => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_empty_inputs() {
        assert_eq!(verify_raw(&[], &[], &[]), 0);
    }
}
