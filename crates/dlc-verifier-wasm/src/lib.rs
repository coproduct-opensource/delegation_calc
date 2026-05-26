//! wasm32 wrapper. M3.M21 wires in `wasm-bindgen`. Skeleton for Week-1.

#![forbid(unsafe_code)]

/// Verify a wire-format proof. Returns 1 on success, 0 on failure. JS bindings
/// (M3.M21) translate this into a richer return shape via `wasm-bindgen`.
pub fn verify_raw(wire: &[u8], claimed: &[u8], keyring: &[u8]) -> u32 {
    let _ = (wire, claimed, keyring);
    0
}
