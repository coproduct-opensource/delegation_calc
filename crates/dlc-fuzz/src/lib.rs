//! Fuzz harnesses. Targets:
//!   - `decide_pure` on arbitrary inputs (no panic, no UB)
//!   - wire-format decode (no panic, bounded memory)
//!   - verifier on arbitrary wire bytes (no panic, deterministic)
//!
//! cargo-fuzz targets land under `fuzz/fuzz_targets/` per harness; the harness
//! library lives here so multiple targets can share corpus utilities.
