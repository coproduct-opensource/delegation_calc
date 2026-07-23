/-
T2 — Cryptographic correspondence: the honest symbolic characterization.

This file proves, WITHOUT AXIOMS, the propositional-fragment
characterization of the cryptographic typing judgment:

  `DerivCrypto K Γₐ M φ`  ⟺  `PropDeriv Γₐ M φ` ∧ `M.allSigsVerify K`

i.e. a term crypto-typechecks under keyring `K` exactly when it
logically typechecks AND every signature embedded in it verifies
under `K`. Both directions are constructive inductions; `#print
axioms t2_propositional_correspondence` reports only `propext`.

## What this is, and what it is not

This is a *symbolic, definitional-refinement* correspondence: the
cryptographic judgment is `PropDeriv` refined with a verification
premise on `says-I`, and the theorem characterizes exactly what that
refinement adds. It is the same class of result as Aura's (Jia et al.,
ICFP 2008) definitional logic↔signature correspondence. It is NOT a
cryptographic soundness theorem: there is no attacker, no key
compromise, no serialization injectivity, and no unforgeability
reduction here.

## Open problems (tracked in the ledger; Phase-4 scope)

The attacker-based T2 — "verifier acceptance implies a derivation from
the assumptions of principals whose keys are uncompromised, against an
explicit Dolev-Yao adversary, by reduction to EUF-CMA" — is OPEN. It
requires (a) an executable verifier (Phase 1), (b) wire-encoding
injectivity for the real CBOR codec (Phase 3), and (c) an EasyCrypt/
SSProve EUF-CMA reduction (Phase 4, collaborator-gated). No statement
of it appears in this file because no honest statement of it can yet
be made against real artifacts.

## History

An earlier revision of this file postulated
`axiom Sig_EUF_CMA_propositional : M.isPropositional = true →
Nonempty (Deriv Γ M φ) → Nonempty (DerivCrypto K Γ M φ)` over a
6-constructor `DerivCrypto`. That axiom was REFUTABLE in-system:
`isPropositional` accepts `pair`-subject terms which the 6-constructor
judgment provably cannot inhabit, so the theory including the axiom
proved `False`. The machine-checked refutation is preserved as a
regression test in `DLC.Witness.AxiomAudit`. The axiom is deleted, not
repaired: the lifting direction is now the *proven*
`t2_logical_to_crypto`, whose extra hypothesis (`allSigsVerify`) makes
explicit exactly what the axiom silently assumed.
-/

import DLC.Judgment
import DLC.Decidability

namespace DLC

/-! ## Crypto operators (abstract; bound to real implementations in Phase 1).

`canonicalBytes` is the deterministic byte encoding of a Term used for
signing; it mirrors what `crates/dlc-crypto`'s canonical-bytes function
must compute (currently stubbed in Rust — see the ledger's crypto
status). `verifyInKeyring` decides signature validity for a
principal-message pair under a keyring. Both are `opaque`: the
characterization below is structural and holds for every
interpretation of these constants. -/

/-- Deterministic byte encoding of a Term suitable for signing. -/
opaque canonicalBytes : Term → List UInt8

/-- Decide whether `sig` is a valid signature by `p` on `m` under `K`. -/
opaque verifyInKeyring : KeyRing → Principal → List UInt8 → Signature → Bool

/-! ## `allSigsVerify` — the signature-validity content of crypto typing.

A term satisfies `allSigsVerify K` when every `sign` node it contains
carries a signature that verifies (under `K`) against the canonical
bytes of the signed subterm. This is precisely the delta between
logical and cryptographic typing in the propositional fragment — see
`t2_propositional_correspondence`. -/

/-- Every `sign` node embedded in the term verifies under `K`. -/
def Term.allSigsVerify (K : KeyRing) : Term → Bool
  | Term.var _            => true
  | Term.lam _ body       => body.allSigsVerify K
  | Term.app f x          => f.allSigsVerify K && x.allSigsVerify K
  | Term.sign p m sig     =>
      verifyInKeyring K p (canonicalBytes m) sig && m.allSigsVerify K
  | Term.verify _ m _     => m.allSigsVerify K
  | Term.delegate m n     => m.allSigsVerify K && n.allSigsVerify K
  | Term.attenuate m _    => m.allSigsVerify K
  -- Both sub-terms must be walked. Omitting this arm would let a `sign`
  -- nested inside a boxed proof escape verification, the obligation acting
  -- as a check shield -- the same hole rustc caught in the Rust mirror
  -- (`dlc-verifier/src/check.rs`) during R2c.
  | Term.boxed _ m n      => m.allSigsVerify K && n.allSigsVerify K
  | Term.discharge m n    => m.allSigsVerify K && n.allSigsVerify K
  | Term.liftLabel _ m    => m.allSigsVerify K
  | Term.declassify _ m π => m.allSigsVerify K && π.allSigsVerify K
  | Term.now _            => true
  | Term.withinIntro _ m  => m.allSigsVerify K
  | Term.pair a b         => a.allSigsVerify K && b.allSigsVerify K
  | Term.fst a            => a.allSigsVerify K
  | Term.snd a            => a.allSigsVerify K
  | Term.inl _ a          => a.allSigsVerify K
  | Term.inr _ a          => a.allSigsVerify K
  | Term.case s l r       =>
      s.allSigsVerify K && l.allSigsVerify K && r.allSigsVerify K
  | Term.tensorIntro a b  => a.allSigsVerify K && b.allSigsVerify K
  | Term.letTensor s b    => s.allSigsVerify K && b.allSigsVerify K
  | Term.saysBind _ s b    => s.allSigsVerify K && b.allSigsVerify K
  | Term.letSays _ s b    => s.allSigsVerify K && b.allSigsVerify K
  | Term.sfExtract m      => m.allSigsVerify K
  -- command(M, c, ℓ): walk BOTH subterms so a `sign` nested in the payload or
  -- the credential is still signature-checked (mirrors the Rust verifier's
  -- `all_sigs_verify` command arm; only `sign` itself carries a signature).
  | Term.command m c _    => m.allSigsVerify K && c.allSigsVerify K

/-! ## `DerivCrypto K` — the cryptographic typing judgment.

Mirrors `PropDeriv` (the syntax-directed propositional-fragment
judgment from `DLC.Decidability`) constructor-for-constructor, with
one difference: `saysI` carries the verification premise
`verifyInKeyring K p (canonicalBytes M) sig = true`.

`PropDeriv` (not the full `Deriv`) is the right base because it is
syntax-directed: each subject shape has exactly one applicable rule,
so the refinement adds the signature check and nothing else. Mirroring
the full `Deriv` is not possible without re-importing the
inconsistency documented in `DLC.Witness.AxiomAudit` — `Deriv` has
rules (`withinE`, the placeholder-subject `saysE`/`boxI`) that re-type
subjects the cryptographic side cannot re-derive. -/
inductive DerivCrypto (K : KeyRing) : List Prop' → Term → Prop' → Type where
  /-- `var-A` — additive variable lookup. -/
  | varA (Γₐ : List Prop') (i : Nat) (φ : Prop')
      (h : Γₐ[i]? = some φ) :
      DerivCrypto K Γₐ (Term.var i) φ

  /-- `imp-I` — implication introduction. -/
  | impI (Γₐ : List Prop') (φ ψ : Prop') (M : Term)
      (d : DerivCrypto K (φ :: Γₐ) M ψ) :
      DerivCrypto K Γₐ (Term.lam φ M) (Prop'.imp φ ψ)

  /-- `imp-E` — implication elimination. -/
  | impE (Γₐ : List Prop') (φ ψ : Prop') (M N : Term)
      (dM : DerivCrypto K Γₐ M (Prop'.imp φ ψ))
      (dN : DerivCrypto K Γₐ N φ) :
      DerivCrypto K Γₐ (Term.app M N) ψ

  /-- `says-I` with cryptographic side condition. THIS is the rule
  that distinguishes `DerivCrypto K` from `PropDeriv`: the embedded
  signature must verify under `K` against the canonical bytes of the
  signed subterm. -/
  | saysI (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
          (sig : Signature)
      (d : DerivCrypto K Γₐ M φ)
      (hver : verifyInKeyring K p (canonicalBytes M) sig = true) :
      DerivCrypto K Γₐ (Term.sign p M sig) (Prop'.says p φ)

  /-- `verify` — `says`-elimination. Strips the modality; the
  introduction-side check (`saysI.hver`) is where signature validity
  is enforced. -/
  | verifyE (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
            (sig : Signature)
      (d : DerivCrypto K Γₐ M (Prop'.says p φ)) :
      DerivCrypto K Γₐ (Term.verify p M sig) φ

  /-- `and-I` — additive conjunction introduction (pair). -/
  | andI (Γₐ : List Prop') (φ ψ : Prop') (a b : Term)
      (dA : DerivCrypto K Γₐ a φ)
      (dB : DerivCrypto K Γₐ b ψ) :
      DerivCrypto K Γₐ (Term.pair a b) (Prop'.and φ ψ)

  /-- `and-E-left` — left projection. -/
  | andEL (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : DerivCrypto K Γₐ a (Prop'.and φ ψ)) :
      DerivCrypto K Γₐ (Term.fst a) φ

  /-- `and-E-right` — right projection. -/
  | andER (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : DerivCrypto K Γₐ a (Prop'.and φ ψ)) :
      DerivCrypto K Γₐ (Term.snd a) ψ

  /-- `within-I` — wrap `φ` with the time modality `◇_τ`. -/
  | withinI (Γₐ : List Prop') (τ : TimeBound) (φ : Prop') (M : Term)
      (d : DerivCrypto K Γₐ M φ) :
      DerivCrypto K Γₐ (Term.withinIntro τ M) (Prop'.within τ φ)

  /-- `or-I-left` — inject into the left disjunct. -/
  | orI_L (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : DerivCrypto K Γₐ a φ) :
      DerivCrypto K Γₐ (Term.inl ψ a) (Prop'.or φ ψ)

  /-- `or-I-right` — inject into the right disjunct. -/
  | orI_R (Γₐ : List Prop') (φ ψ : Prop') (a : Term)
      (d : DerivCrypto K Γₐ a ψ) :
      DerivCrypto K Γₐ (Term.inr φ a) (Prop'.or φ ψ)

  /-- `tensor-I` — multiplicative conjunction (additive shape in the
  propositional fragment). -/
  | tensorI (Γₐ : List Prop') (φ ψ : Prop') (a b : Term)
      (dA : DerivCrypto K Γₐ a φ)
      (dB : DerivCrypto K Γₐ b ψ) :
      DerivCrypto K Γₐ (Term.tensorIntro a b) (Prop'.tensor φ ψ)

  /-- `or-E` — case-elimination of a disjunction. -/
  | orE (Γₐ : List Prop') (φ ψ χ : Prop') (S L R : Term)
      (dS : DerivCrypto K Γₐ S (Prop'.or φ ψ))
      (dL : DerivCrypto K (φ :: Γₐ) L χ)
      (dR : DerivCrypto K (ψ :: Γₐ) R χ) :
      DerivCrypto K Γₐ (Term.case S L R) χ

  /-- `says-extract` — let-binder form of says-elim. -/
  | letSaysE (Γₐ : List Prop') (p : Principal) (φ ψ : Prop') (S B : Term)
      (dS : DerivCrypto K Γₐ S (Prop'.says p φ))
      (dB : DerivCrypto K (φ :: Γₐ) B ψ) :
      DerivCrypto K Γₐ (Term.letSays p S B) ψ

  /-- `sf-extract` — extract a speaks-for from `p says (q ⇒ p)`. -/
  | sfExtractE (Γₐ : List Prop') (p q : Principal) (M : Term)
      (d : DerivCrypto K Γₐ M (Prop'.says p (Prop'.speaksFor q p))) :
      DerivCrypto K Γₐ (Term.sfExtract M) (Prop'.speaksFor q p)

  /-- `delegate` — chain composition; no-splicing is built into the
  constructor's principal indices, exactly as in `PropDeriv.delegate`. -/
  | delegate (Γₐ : List Prop') (p q : Principal) (φ : Prop') (M N : Term)
      (dM : DerivCrypto K Γₐ M (Prop'.says p (Prop'.speaksFor q p)))
      (dN : DerivCrypto K Γₐ N (Prop'.says q φ)) :
      DerivCrypto K Γₐ (Term.delegate M N)
                       (Prop'.says (Principal.acting p q) φ)

  /-- `now τ` — unit-like introduction form for `Top`. -/
  | now (Γₐ : List Prop') (τ : TimeBound) :
      DerivCrypto K Γₐ (Term.now τ) Prop'.top

  /-- `attenuate` (degenerate form) — mirrors `PropDeriv.attenuate`. -/
  | attenuate (Γₐ : List Prop') (p : Principal) (φ : Prop') (M : Term)
      (d : DerivCrypto K Γₐ M (Prop'.says p φ)) :
      DerivCrypto K Γₐ (Term.attenuate M φ) (Prop'.says p φ)

  /-- `lift_ℓ(M)` — IFC label introduction. -/
  | liftLabel (Γₐ : List Prop') (φ : Prop') (ℓ : Label) (M : Term)
      (d : DerivCrypto K Γₐ M φ) :
      DerivCrypto K Γₐ (Term.liftLabel ℓ M) (Prop'.at φ ℓ)

  /-- `declassify_ℓ'(M, π)` — controlled IFC label lowering. -/
  | declassify (Γₐ : List Prop') (φ : Prop') (ℓ ℓ' : Label) (M π : Term)
      (d : DerivCrypto K Γₐ M (Prop'.at φ ℓ))
      (dπ : DerivCrypto K Γₐ π (Prop'.atom 0)) :
      DerivCrypto K Γₐ (Term.declassify ℓ' M π) (Prop'.at φ ℓ')

  /-- `discharge(M, N)` — `□_O φ` elimination. Dead in the
  propositional fragment for the same reason as `PropDeriv.discharge`
  (no `boxI`); kept for syntactic completeness. -/
  | discharge (Γₐ : List Prop') (O : Obligation) (φ : Prop') (M N : Term)
      (dM : DerivCrypto K Γₐ M (Prop'.boxed O φ))
      (dN : DerivCrypto K Γₐ N (Prop'.atom 0)) :
      DerivCrypto K Γₐ (Term.discharge M N) φ

  /-- `let x⊗y = S in B` — tensor elimination (additive variant). -/
  | letTensor (Γₐ : List Prop') (φ ψ χ : Prop') (S B : Term)
      (dS : DerivCrypto K Γₐ S (Prop'.tensor φ ψ))
      (dB : DerivCrypto K (φ :: ψ :: Γₐ) B χ) :
      DerivCrypto K Γₐ (Term.letTensor S B) χ

/-! ## Direction 1 — crypto typing erases to logical typing. -/

/-- Erase the verification premises; the result is a `PropDeriv`.
`noncomputable def` because both judgments are `Type`-valued (the
result is a constructive map between derivation trees). -/
noncomputable def t2_crypto_to_logical (K : KeyRing)
    {Γₐ : List Prop'} {M : Term} {φ : Prop'}
    (dc : DerivCrypto K Γₐ M φ) : PropDeriv Γₐ M φ := by
  induction dc with
  | varA Γₐ i φ h => exact .varA Γₐ i φ h
  | impI Γₐ φ ψ M _ ih => exact .impI Γₐ φ ψ M ih
  | impE Γₐ φ ψ M N _ _ ihM ihN => exact .impE Γₐ φ ψ M N ihM ihN
  | saysI Γₐ p φ M sig _ _ ih => exact .saysI Γₐ p φ M sig ih
  | verifyE Γₐ p φ M sig _ ih => exact .verifyE Γₐ p φ M sig ih
  | andI Γₐ φ ψ a b _ _ ihA ihB => exact .andI Γₐ φ ψ a b ihA ihB
  | andEL Γₐ φ ψ a _ ih => exact .andEL Γₐ φ ψ a ih
  | andER Γₐ φ ψ a _ ih => exact .andER Γₐ φ ψ a ih
  | withinI Γₐ τ φ M _ ih => exact .withinI Γₐ τ φ M ih
  | orI_L Γₐ φ ψ a _ ih => exact .orI_L Γₐ φ ψ a ih
  | orI_R Γₐ φ ψ a _ ih => exact .orI_R Γₐ φ ψ a ih
  | tensorI Γₐ φ ψ a b _ _ ihA ihB => exact .tensorI Γₐ φ ψ a b ihA ihB
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
      exact .orE Γₐ φ ψ χ S L R ihS ihL ihR
  | letSaysE Γₐ p φ ψ S B _ _ ihS ihB =>
      exact .letSaysE Γₐ p φ ψ S B ihS ihB
  | sfExtractE Γₐ p q M _ ih => exact .sfExtractE Γₐ p q M ih
  | delegate Γₐ p q φ M N _ _ ihM ihN =>
      exact .delegate Γₐ p q φ M N ihM ihN
  | now Γₐ τ => exact .now Γₐ τ
  | attenuate Γₐ p φ M _ ih => exact .attenuate Γₐ p φ M ih
  | liftLabel Γₐ φ ℓ M _ ih => exact .liftLabel Γₐ φ ℓ M ih
  | declassify Γₐ φ ℓ ℓ' M π _ _ ihM ihπ =>
      exact .declassify Γₐ φ ℓ ℓ' M π ihM ihπ
  | discharge Γₐ O φ M N _ _ ihM ihN =>
      exact .discharge Γₐ O φ M N ihM ihN
  | letTensor Γₐ φ ψ χ S B _ _ ihS ihB =>
      exact .letTensor Γₐ φ ψ χ S B ihS ihB

/-- Crypto typing implies every embedded signature verifies. Together
with `t2_crypto_to_logical` this is the forward half of the
characterization: crypto typing carries exactly the logical derivation
plus signature validity, nothing more. -/
theorem t2_crypto_sigs_verify (K : KeyRing)
    {Γₐ : List Prop'} {M : Term} {φ : Prop'}
    (dc : DerivCrypto K Γₐ M φ) : M.allSigsVerify K = true := by
  induction dc with
  | varA Γₐ i φ h => rfl
  | impI Γₐ φ ψ M _ ih => simpa [Term.allSigsVerify] using ih
  | impE Γₐ φ ψ M N _ _ ihM ihN =>
      simp [Term.allSigsVerify, ihM, ihN]
  | saysI Γₐ p φ M sig _ hver ih =>
      simp [Term.allSigsVerify, hver, ih]
  | verifyE Γₐ p φ M sig _ ih => simpa [Term.allSigsVerify] using ih
  | andI Γₐ φ ψ a b _ _ ihA ihB =>
      simp [Term.allSigsVerify, ihA, ihB]
  | andEL Γₐ φ ψ a _ ih => simpa [Term.allSigsVerify] using ih
  | andER Γₐ φ ψ a _ ih => simpa [Term.allSigsVerify] using ih
  | withinI Γₐ τ φ M _ ih => simpa [Term.allSigsVerify] using ih
  | orI_L Γₐ φ ψ a _ ih => simpa [Term.allSigsVerify] using ih
  | orI_R Γₐ φ ψ a _ ih => simpa [Term.allSigsVerify] using ih
  | tensorI Γₐ φ ψ a b _ _ ihA ihB =>
      simp [Term.allSigsVerify, ihA, ihB]
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
      simp [Term.allSigsVerify, ihS, ihL, ihR]
  | letSaysE Γₐ p φ ψ S B _ _ ihS ihB =>
      simp [Term.allSigsVerify, ihS, ihB]
  | sfExtractE Γₐ p q M _ ih => simpa [Term.allSigsVerify] using ih
  | delegate Γₐ p q φ M N _ _ ihM ihN =>
      simp [Term.allSigsVerify, ihM, ihN]
  | now Γₐ τ => rfl
  | attenuate Γₐ p φ M _ ih => simpa [Term.allSigsVerify] using ih
  | liftLabel Γₐ φ ℓ M _ ih => simpa [Term.allSigsVerify] using ih
  | declassify Γₐ φ ℓ ℓ' M π _ _ ihM ihπ =>
      simp [Term.allSigsVerify, ihM, ihπ]
  | discharge Γₐ O φ M N _ _ ihM ihN =>
      simp [Term.allSigsVerify, ihM, ihN]
  | letTensor Γₐ φ ψ χ S B _ _ ihS ihB =>
      simp [Term.allSigsVerify, ihS, ihB]

/-! ## Direction 2 — logical typing plus signature validity lifts. -/

/-- A logical derivation whose subject's embedded signatures all verify
lifts to a cryptographic derivation. This PROVEN lemma replaces the
deleted `Sig_EUF_CMA_propositional` axiom; the `allSigsVerify`
hypothesis is exactly what that axiom silently (and, over the full
`Deriv`, inconsistently) assumed. -/
noncomputable def t2_logical_to_crypto (K : KeyRing)
    {Γₐ : List Prop'} {M : Term} {φ : Prop'}
    (d : PropDeriv Γₐ M φ) :
    M.allSigsVerify K = true → DerivCrypto K Γₐ M φ := by
  induction d with
  | varA Γₐ i φ h => exact fun _ => .varA Γₐ i φ h
  | impI Γₐ φ ψ M _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .impI Γₐ φ ψ M (ih hsig)
  | impE Γₐ φ ψ M N _ _ ihM ihN =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .impE Γₐ φ ψ M N (ihM hsig.1) (ihN hsig.2)
  | saysI Γₐ p φ M sig _ ih =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .saysI Γₐ p φ M sig (ih hsig.2) hsig.1
  | verifyE Γₐ p φ M sig _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .verifyE Γₐ p φ M sig (ih hsig)
  | andI Γₐ φ ψ a b _ _ ihA ihB =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .andI Γₐ φ ψ a b (ihA hsig.1) (ihB hsig.2)
  | andEL Γₐ φ ψ a _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .andEL Γₐ φ ψ a (ih hsig)
  | andER Γₐ φ ψ a _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .andER Γₐ φ ψ a (ih hsig)
  | withinI Γₐ τ φ M _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .withinI Γₐ τ φ M (ih hsig)
  | orI_L Γₐ φ ψ a _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .orI_L Γₐ φ ψ a (ih hsig)
  | orI_R Γₐ φ ψ a _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .orI_R Γₐ φ ψ a (ih hsig)
  | tensorI Γₐ φ ψ a b _ _ ihA ihB =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .tensorI Γₐ φ ψ a b (ihA hsig.1) (ihB hsig.2)
  | orE Γₐ φ ψ χ S L R _ _ _ ihS ihL ihR =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .orE Γₐ φ ψ χ S L R (ihS hsig.1.1) (ihL hsig.1.2) (ihR hsig.2)
  | letSaysE Γₐ p φ ψ S B _ _ ihS ihB =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .letSaysE Γₐ p φ ψ S B (ihS hsig.1) (ihB hsig.2)
  | sfExtractE Γₐ p q M _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .sfExtractE Γₐ p q M (ih hsig)
  | delegate Γₐ p q φ M N _ _ ihM ihN =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .delegate Γₐ p q φ M N (ihM hsig.1) (ihN hsig.2)
  | now Γₐ τ => exact fun _ => .now Γₐ τ
  | attenuate Γₐ p φ M _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .attenuate Γₐ p φ M (ih hsig)
  | liftLabel Γₐ φ ℓ M _ ih =>
      intro hsig
      simp only [Term.allSigsVerify] at hsig
      exact .liftLabel Γₐ φ ℓ M (ih hsig)
  | declassify Γₐ φ ℓ ℓ' M π _ _ ihM ihπ =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .declassify Γₐ φ ℓ ℓ' M π (ihM hsig.1) (ihπ hsig.2)
  | discharge Γₐ O φ M N _ _ ihM ihN =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .discharge Γₐ O φ M N (ihM hsig.1) (ihN hsig.2)
  | letTensor Γₐ φ ψ χ S B _ _ ihS ihB =>
      intro hsig
      simp only [Term.allSigsVerify, Bool.and_eq_true] at hsig
      exact .letTensor Γₐ φ ψ χ S B (ihS hsig.1) (ihB hsig.2)

/-! ## T2 — the symbolic characterization theorem. -/

/-- T2 (symbolic characterization, propositional fragment). A term
crypto-typechecks under `K` iff it logically typechecks and every
embedded signature verifies under `K`. Axiom-free; see the module
docstring for what this does and does not claim. -/
theorem t2_propositional_correspondence
    (K : KeyRing) (Γₐ : List Prop') (M : Term) (φ : Prop') :
    Nonempty (DerivCrypto K Γₐ M φ) ↔
      Nonempty (PropDeriv Γₐ M φ) ∧ M.allSigsVerify K = true := by
  constructor
  · intro ⟨dc⟩
    exact ⟨⟨t2_crypto_to_logical K dc⟩, t2_crypto_sigs_verify K dc⟩
  · intro ⟨⟨d⟩, hsig⟩
    exact ⟨t2_logical_to_crypto K d hsig⟩

/-! ## Sanity checks. -/

namespace CorrespondenceChecks

/-- Look up the only hypothesis in a singleton context — the crypto
version. No signature nodes, so no verification obligations. -/
example (K : KeyRing) :
    DerivCrypto K [Prop'.atom 0] (Term.var 0) (Prop'.atom 0) :=
  DerivCrypto.varA _ 0 _ rfl

/-- Erasure applied to the trivial witness above. -/
noncomputable example (K : KeyRing) :
    PropDeriv [Prop'.atom 0] (Term.var 0) (Prop'.atom 0) :=
  t2_crypto_to_logical K (DerivCrypto.varA _ 0 _ rfl)

/-- A signature-free term crypto-typechecks iff it typechecks:
`allSigsVerify` is definitionally `true` on `var`. -/
example (K : KeyRing) :
    Nonempty (DerivCrypto K [Prop'.atom 0] (Term.var 0) (Prop'.atom 0)) ↔
      Nonempty (PropDeriv [Prop'.atom 0] (Term.var 0) (Prop'.atom 0)) ∧
        (Term.var 0).allSigsVerify K = true :=
  t2_propositional_correspondence K _ _ _

end CorrespondenceChecks

end DLC
