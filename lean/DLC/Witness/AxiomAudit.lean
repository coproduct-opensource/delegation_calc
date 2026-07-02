/-
Axiom audit — machine-checked refutation of the legacy T2 axiom.

The 2026-07 external audit found that the then-current
`axiom Sig_EUF_CMA_propositional` was refutable inside the system:
it quantified over every term with `isPropositional = true` (which
accepts `pair`-subject terms, e.g. via `Deriv.andI`), while the
6-constructor `DerivCrypto` of that revision could only inhabit
`var`/`lam`/`app`/`sign` subjects. The axiom therefore asserted
`Nonempty` of an empty type, and the theory including it proved
`False`.

This file preserves that finding as a regression test:

* `LegacyDerivCrypto` is the 6-constructor judgment, verbatim.
* `LegacyAxiomStatement` is the deleted axiom's statement, verbatim.
* `legacy_axiom_refutable : LegacyAxiomStatement → False` is the
  machine-checked refutation.

The repaired development (`DLC.Correspondence`) has no such axiom: the
lifting direction is proven outright with an explicit `allSigsVerify`
hypothesis. This file guards against the axiom's shape being
reintroduced — any future assumption of the form
"logical derivation ⇒ crypto derivation, hypothesized only on a
subject-term predicate" must contend with `legacy_axiom_refutable`.
-/

import DLC.Judgment
import DLC.Decidability
import DLC.Correspondence

namespace DLC.Witness

open DLC

/-- The legacy 6-constructor cryptographic judgment, exactly as it
stood when the refuted axiom was in force (over full `Ctx`, with
linear-context splitting on `impE`). Preserved only for the
refutation below; the live judgment is `DLC.DerivCrypto`. -/
inductive LegacyDerivCrypto (K : KeyRing) : Ctx → Term → Prop' → Type where
  | varA (Γ : Ctx) (i : Nat) (φ : Prop')
      (h : Γ.additive[i]? = some φ) :
      LegacyDerivCrypto K Γ (Term.var i) φ
  | varL (Γₐ : List Prop') (φ : Prop') :
      LegacyDerivCrypto K { additive := Γₐ, linear := [φ] } (Term.var 0) φ
  | weakenA (Γ : Ctx) (φ' φ : Prop') (M : Term)
      (d : LegacyDerivCrypto K Γ M φ) :
      LegacyDerivCrypto K (Ctx.consA φ' Γ) M φ
  | impI (Γ : Ctx) (φ ψ : Prop') (M : Term)
      (d : LegacyDerivCrypto K (Ctx.consA φ Γ) M ψ) :
      LegacyDerivCrypto K Γ (Term.lam φ M) (Prop'.imp φ ψ)
  | impE (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (φ ψ : Prop') (M N : Term)
      (dM : LegacyDerivCrypto K { additive := Γₐ, linear := Γ₁ } M
              (Prop'.imp φ ψ))
      (dN : LegacyDerivCrypto K { additive := Γₐ, linear := Γ₂ } N φ) :
      LegacyDerivCrypto K { additive := Γₐ, linear := Γ₁ ++ Γ₂ }
                        (Term.app M N) ψ
  | saysI (Γ : Ctx) (p : Principal) (φ : Prop') (M : Term) (sig : Signature)
      (d : LegacyDerivCrypto K Γ M φ)
      (hver : verifyInKeyring K p (canonicalBytes M) sig = true) :
      LegacyDerivCrypto K Γ (Term.sign p M sig) (Prop'.says p φ)

/-- The deleted axiom's statement, verbatim (modulo the judgment
rename). Asserting this as an axiom made the theory inconsistent —
see `legacy_axiom_refutable`. -/
def LegacyAxiomStatement : Prop :=
  ∀ (K : KeyRing) (Γ : Ctx) (M : Term) (φ : Prop'),
    M.isPropositional = true →
    Nonempty (Deriv Γ M φ) →
    Nonempty (LegacyDerivCrypto K Γ M φ)

/-- No legacy-crypto derivation has a `pair` subject: every
constructor's subject is `var`, `lam`, `app`, or `sign` (with
`weakenA` preserving its premise's subject). -/
theorem legacy_no_pair_subject {K : KeyRing} {Γ : Ctx} {M : Term}
    {φ : Prop'} (d : LegacyDerivCrypto K Γ M φ) :
    ∀ (a b : Term), M = Term.pair a b → False := by
  induction d with
  | varA Γ i φ h => intro a b h'; cases h'
  | varL Γₐ φ => intro a b h'; cases h'
  | weakenA Γ φ' φ M _ ih => intro a b h'; exact ih a b h'
  | impI Γ φ ψ M _ _ => intro a b h'; cases h'
  | impE Γₐ Γ₁ Γ₂ φ ψ M N _ _ _ _ => intro a b h'; cases h'
  | saysI Γ p φ M sig _ _ _ => intro a b h'; cases h'

/-- THE AUDIT FINDING, machine-checked: the legacy axiom statement
implies `False`. Witness: `pair (var 0) (var 1)` is `isPropositional`
and `Deriv`-typeable (via `andI`) in the context `[atom 0, atom 1]`,
but no `LegacyDerivCrypto` inhabitant can have a `pair` subject. -/
theorem legacy_axiom_refutable : LegacyAxiomStatement → False := by
  intro hax
  have hd : Nonempty (Deriv
      { additive := [Prop'.atom 0, Prop'.atom 1], linear := [] }
      (Term.pair (Term.var 0) (Term.var 1))
      (Prop'.and (Prop'.atom 0) (Prop'.atom 1))) :=
    ⟨Deriv.andI [Prop'.atom 0, Prop'.atom 1] (Prop'.atom 0) (Prop'.atom 1)
      (Term.var 0) (Term.var 1)
      (Deriv.varA _ 0 _ rfl) (Deriv.varA _ 1 _ rfl)⟩
  have hprop :
      (Term.pair (Term.var 0) (Term.var 1)).isPropositional = true := rfl
  obtain ⟨dc⟩ := hax ⟨[]⟩ _ _ _ hprop hd
  exact legacy_no_pair_subject dc _ _ rfl

end DLC.Witness
