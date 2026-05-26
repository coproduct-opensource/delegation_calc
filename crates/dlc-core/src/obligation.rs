//! Linear obligations.
//!
//! Once discharged, consumed — this is what makes obligation tracking sound
//! across reduction (T4). The production realization mirrors nucleus's
//! `DischargedBundle` sealed-constructor pattern.

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::principal::Principal;
use crate::time::TimeBound;

/// An obligation expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obligation {
    /// ⊤ — trivially discharged.
    Top,
    /// ⊥ — un-dischargeable; presence forces non-progress.
    Bot,
    /// `act_of(p, action)` — principal p must perform `action`.
    ActOf(Principal, ActionId),
    /// `within(τ)` — must be discharged before time τ.
    Within(TimeBound),
    /// `O₁ ⊗ O₂` — both must be discharged.
    Tensor(Box<Obligation>, Box<Obligation>),
    /// `O₁ ⊸ O₂` — if O₁ is discharged, O₂ becomes due.
    Lolli(Box<Obligation>, Box<Obligation>),
}

/// Opaque identifier for an action; resolved by the runtime obligation table.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ActionId(pub Vec<u8>);
