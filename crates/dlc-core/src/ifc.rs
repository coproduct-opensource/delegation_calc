//! IFC labels.
//!
//! In production (Phase 3), `Label` is replaced by a re-export of nucleus's
//! 13-dimensional `PermissionLattice` so the Lean proofs in
//! `lean/PortcullisCoreImport.lean` apply directly. For Week-1 we carry a
//! placeholder so the type signatures in `Prop` compile.

use alloc::vec::Vec;

/// An IFC label. The placeholder structure is a sorted vector of capability
/// indices; the 13-dim nucleus lattice slots in as the production
/// implementation at M1.Q4.a.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label(pub Vec<u32>);

impl Label {
    /// `⊥ℓ` — the bottom label (public / least authority).
    pub fn bottom() -> Self {
        Label(Vec::new())
    }

    /// `ℓ₁ ⊔ ℓ₂` — lattice join.
    pub fn join(&self, other: &Self) -> Self {
        let mut v = self.0.clone();
        v.extend_from_slice(&other.0);
        v.sort();
        v.dedup();
        Label(v)
    }
}
