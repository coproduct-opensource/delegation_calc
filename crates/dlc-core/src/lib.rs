//! Delegation Logic Calculus — logic kernel.
//!
//! This crate is the Aeneas/Charon translation target. Its Lean image carries
//! the four headline theorems (T1 decidability, T2 cryptographic
//! correspondence, T3 non-interference, T4 obligation soundness). To keep the
//! bridge clean:
//!
//!   * No trait objects (`dyn Trait`).
//!   * No `async` / futures.
//!   * No interior mutability beyond what Aeneas's translation supports.
//!   * No third-party dependencies. Only `core` and `alloc`.
//!   * No `unsafe`.
//!
//! Violations break the Rust↔Lean bridge silently — T1 would then be a theorem
//! about a Lean function no longer corresponding to this Rust. CI enforces
//! these via `scripts/check-drift.sh` (Aeneas regeneration + diff).

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate alloc;

pub mod syntax;
pub mod judgment;
pub mod principal;
pub mod ifc;
pub mod obligation;
pub mod time;
pub mod subst;
pub mod reduce;
pub mod decide;
