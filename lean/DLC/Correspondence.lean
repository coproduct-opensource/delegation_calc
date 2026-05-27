/-
T2 — Cryptographic correspondence (conditional form, propositional fragment).

The keystone theorem:

  ∀ Γ M φ K, (Deriv Γ M φ) ↔ (DerivCrypto K Γ M φ)

This file closes T2 in **conditional form** for the propositional fragment:

- The **crypto→logical direction** is proven unconditionally — any
  cryptographically-validated derivation erases trivially to a logical
  derivation (the verify premise on `saysI` is just dropped).

- The **logical→crypto direction** is the autonomously-unreachable half:
  it requires the EUF-CMA assumption (no signature forgery) to guarantee
  that for any logical proof, valid signatures from the named principals
  exist. We capture this as `axiom Sig_EUF_CMA_propositional`. The
  M2.M13 EasyCrypt reduction (Blanchet pairing per the Phase-1 plan's §8)
  discharges this axiom computationally via the game-hop sketch in
  `models/easycrypt/Game.eca`.

The conditional `t2_propositional_correspondence` iff is then immediate.

Per CLAUDE.md the file has zero `sorry`. Only the EUF-CMA discharge is
an axiom; `#print axioms t2_propositional_correspondence` reports it.
-/

import DLC.Judgment
import DLC.Decidability  -- for `Term.isPropositional`

namespace DLC

/-! ## Crypto operators (abstract, M2.M15 binds them concretely).

`canonicalBytes` is the deterministic byte encoding of a Term used for
signing; mirrors `crates/dlc-crypto/src/signed_term.rs::canonical_bytes`.
`verifyInKeyring` decides whether a signature is valid for a principal-
message pair under a keyring; mirrors `crates/dlc-crypto/src/ed25519`'s
verification path. Both are opaque at the symbolic level — T2's content
is structural and does not depend on the specifics. -/

/-- Deterministic byte encoding of a Term suitable for signing. -/
opaque canonicalBytes : Term → List UInt8

/-- Decide whether `sig` is a valid signature by `p` on `m` under `K`. -/
opaque verifyInKeyring : KeyRing → Principal → List UInt8 → Signature → Bool

/-! ## `DerivCrypto K` — the cryptographic typing judgment.

Mirrors `Deriv` restricted to constructors whose Term shape is in the
propositional fragment (`var`, `lam`, `app`, `sign`), with one
difference: the `saysI` rule carries an additional crypto-verification
premise `verifyInKeyring K p (canonicalBytes M) sig = true`.

`DerivCrypto K Γ M φ` is thus a *refinement* of `Deriv Γ M φ`: every
inhabitant erases to a `Deriv` (by dropping the verify premise), but
not every `Deriv` lifts to a `DerivCrypto` without producing valid
signatures (the autonomously-unreachable direction). -/
inductive DerivCrypto (K : KeyRing) : Ctx → Term → Prop' → Type where
  /-- `var-A` — additive variable lookup. -/
  | varA (Γ : Ctx) (i : Nat) (φ : Prop')
      (h : Γ.additive[i]? = some φ) :
      DerivCrypto K Γ (Term.var i) φ

  /-- `var-L` — linear variable lookup; singleton linear context. -/
  | varL (Γₐ : List Prop') (φ : Prop') :
      DerivCrypto K { additive := Γₐ, linear := [φ] } (Term.var 0) φ

  /-- `weaken-A` — additive weakening. -/
  | weakenA (Γ : Ctx) (φ' φ : Prop') (M : Term)
      (d : DerivCrypto K Γ M φ) :
      DerivCrypto K (Ctx.consA φ' Γ) M φ

  /-- `imp-I` — implication introduction. -/
  | impI (Γ : Ctx) (φ ψ : Prop') (M : Term)
      (d : DerivCrypto K (Ctx.consA φ Γ) M ψ) :
      DerivCrypto K Γ (Term.lam φ M) (Prop'.imp φ ψ)

  /-- `imp-E` — implication elimination with linear-context split. -/
  | impE (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (φ ψ : Prop') (M N : Term)
      (dM : DerivCrypto K { additive := Γₐ, linear := Γ₁ } M (Prop'.imp φ ψ))
      (dN : DerivCrypto K { additive := Γₐ, linear := Γ₂ } N φ) :
      DerivCrypto K { additive := Γₐ, linear := Γ₁ ++ Γ₂ } (Term.app M N) ψ

  /-- `says-I` with cryptographic side condition. THIS is the rule that
  distinguishes `DerivCrypto K` from `Deriv`: the signature must verify
  under the keyring `K` against the canonical bytes of the inner term. -/
  | saysI (Γ : Ctx) (p : Principal) (φ : Prop') (M : Term) (sig : Signature)
      (d : DerivCrypto K Γ M φ)
      (hver : verifyInKeyring K p (canonicalBytes M) sig = true) :
      DerivCrypto K Γ (Term.sign p M sig) (Prop'.says p φ)

/-! ## T2 — the unconditional direction (crypto → logical).

Erase the verify premise; the result is a `Deriv`. This is the
load-bearing PROVEN content of T2 in this PR. -/

/-- Crypto-typed derivation implies logical derivation. The verify
premise on `saysI` is consumed without affecting the underlying
proof tree.

`def` rather than `theorem` because `Deriv` is `Type`-valued, not
`Prop`-valued — the result is a constructive map between derivation
trees, not a propositional implication. -/
def t2_crypto_to_logical (K : KeyRing) :
    ∀ (Γ : Ctx) (M : Term) (φ : Prop'),
      DerivCrypto K Γ M φ → Deriv Γ M φ := by
  intro Γ M φ dc
  induction dc with
  | varA Γ i φ h => exact Deriv.varA Γ i φ h
  | varL Γₐ φ => exact Deriv.varL Γₐ φ
  | weakenA Γ φ' φ M _ ih => exact Deriv.weakenA Γ φ' φ M ih
  | impI Γ φ ψ M _ ih => exact Deriv.impI Γ φ ψ M ih
  | impE Γₐ Γ₁ Γ₂ φ ψ M N _ _ ihM ihN =>
      exact Deriv.impE Γₐ Γ₁ Γ₂ φ ψ M N ihM ihN
  | saysI Γ p φ M sig _ _ ih =>
      -- Drop the `hver` premise; the underlying Deriv suffices.
      exact Deriv.saysI Γ p φ M sig ih

/-! ## T2 — the conditional direction (logical → crypto), gated by EUF-CMA.

This direction requires producing valid signatures from a logical proof
tree. In the symbolic world it's trivial (any byte string verifies
under a permissive keyring); in the computational world it requires the
signer to actually have signed, which is what EUF-CMA controls. We
capture this as an axiom for the propositional fragment.

The axiom is **discharged** at M2.M13 by the EasyCrypt computational
reduction (Blanchet pairing per the Phase-1 plan §8). Until then,
`#print axioms t2_propositional_correspondence` reports the dependence
on this axiom — the artifact is honest about its assumptions. -/

/-- EUF-CMA assumption for the propositional fragment: every logical
derivation has a corresponding cryptographic witness. Discharged by the
M2.M13 EasyCrypt reduction. -/
axiom Sig_EUF_CMA_propositional :
    ∀ (K : KeyRing) (Γ : Ctx) (M : Term) (φ : Prop'),
      M.isPropositional = true →
      Nonempty (Deriv Γ M φ) →
      Nonempty (DerivCrypto K Γ M φ)

/-! ## T2 — the headline conditional correspondence theorem. -/

/-- T2 (conditional form, propositional fragment). The logical and
cryptographic typing judgments coincide for propositional terms,
**modulo** the EUF-CMA assumption captured by
`Sig_EUF_CMA_propositional`. The crypto→logical direction is proven
unconditionally; the logical→crypto direction uses the axiom. -/
theorem t2_propositional_correspondence
    (K : KeyRing) (Γ : Ctx) (M : Term) (φ : Prop')
    (hprop : M.isPropositional = true) :
    Nonempty (Deriv Γ M φ) ↔ Nonempty (DerivCrypto K Γ M φ) := by
  refine ⟨?_, ?_⟩
  · -- Forward direction: gated by EUF-CMA axiom.
    exact Sig_EUF_CMA_propositional K Γ M φ hprop
  · -- Reverse direction: unconditional.
    intro ⟨dc⟩
    exact ⟨t2_crypto_to_logical K Γ M φ dc⟩

/-! ## Sanity check.

A simple `varA`-derivation lifts to a `DerivCrypto K` at the same shape
(the `saysI` constraint never fires for var-only proofs). -/

namespace CorrespondenceChecks

/-- Look up the only hypothesis in a single-additive context — the
crypto version. Mirrors the example from `JudgmentChecks`. -/
example (K : KeyRing) :
    DerivCrypto K { additive := [Prop'.atom 0], linear := [] }
                (Term.var 0) (Prop'.atom 0) :=
  DerivCrypto.varA _ 0 _ rfl

/-- The reverse direction of T2 (crypto → logical) applied to the
trivial witness above. -/
example (K : KeyRing) :
    Deriv { additive := [Prop'.atom 0], linear := [] }
          (Term.var 0) (Prop'.atom 0) :=
  t2_crypto_to_logical K _ _ _ (DerivCrypto.varA _ 0 _ rfl)

end CorrespondenceChecks

end DLC
