//! Principals — humans, agents, services — and their composition operators.

use alloc::boxed::Box;
use alloc::vec::Vec;

/// A principal carries cryptographic identity intrinsically. The `k(p)` form
/// from the spec is the projection `Principal::key_id`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Principal {
    /// Atomic principal identified by stable opaque id (e.g. SPIFFE-ID hash).
    Atom(PrincipalId),
    /// `p ∧ q` — conjunctive principal: both must consent.
    And(Box<Principal>, Box<Principal>),
    /// `p ∨ q` — disjunctive principal: either consents.
    Or(Box<Principal>, Box<Principal>),
    /// `p ⊓ q` — *p acting in q's capacity*. Associative, NOT commutative.
    /// `H ⊓ A ⊓ B` reads as "B acting as A acting as H".
    Acting(Box<Principal>, Box<Principal>),
}

/// Stable identifier for an atomic principal.
///
/// Concrete realization (Phase 3): a SPIFFE-ID truncated SHA-256 (32 bytes).
/// Kept opaque here so dlc-core has no transitive crypto dep.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PrincipalId(pub [u8; 32]);

/// A keyring entry: principal → public-key bytes.
///
/// `Γ ⊢_K M : φ` is parameterized over the keyring K, of which this is one
/// row. Algorithm identifier matches `syntax::Signature::alg`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyRecord {
    /// The atomic principal this key belongs to.
    pub principal: PrincipalId,
    /// Algorithm identifier (e.g. Ed25519 = 0).
    pub alg: u8,
    /// Raw public-key bytes.
    pub public_key: Vec<u8>,
}
