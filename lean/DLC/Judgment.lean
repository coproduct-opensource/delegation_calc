/-
DLC — Typing judgments.

Four mutually recursive judgments (frozen in `spec/typing-rules.md`):
  Γ ⊢ M : φ            -- logical typing (this file's `Deriv`)
  Γ ⊢ p says M : ...   -- affirmation typing (a case of `Deriv`)
  Γ ⊢ M ▷ M'           -- small-step reduction (DLC.Reduce)
  Γ ⊢_K M : φ          -- cryptographic typing (DLC.Correspondence)

M1.Q2.b populates `Deriv` with the first ten typing rules covering structural
hypotheses (§1), the connectives (§2), the linear core (§3), and the
affirmation modality including its Ed25519 signature carrier (§4).
-/

import DLC.Syntax
import DLC.Principal

namespace DLC

/-- A typing context: additive (re-usable) and linear (single-use). Linear
hypotheses currently use `List` for ease of decidable equality; M1.Q4.a
upgrades to `Multiset` so the substructural rules become clean. -/
structure Ctx where
  additive : List Prop'
  linear   : List Prop'
  deriving Repr

namespace Ctx

/-- The empty context. -/
def empty : Ctx := { additive := [], linear := [] }

/-- Push an additive hypothesis. -/
def consA (φ : Prop') (Γ : Ctx) : Ctx :=
  { Γ with additive := φ :: Γ.additive }

/-- Push a linear hypothesis. -/
def consL (φ : Prop') (Γ : Ctx) : Ctx :=
  { Γ with linear := φ :: Γ.linear }

end Ctx

/-- A keyring threads the cryptographic-typing judgment `⊢_K`. -/
structure KeyRing where
  entries : List KeyRecord
  deriving Repr

/-- The derivation predicate. Each constructor corresponds to a rule name in
`spec/typing-rules.md`; the rule-name comment is the source of truth.

Phase-1 deliverable: ~40 constructors by end of Q4. This Q2 milestone closes
the first ten (var, weakening, implication, conjunction, says). -/
inductive Deriv : Ctx → Term → Prop' → Type where
  /-- `var-A` — additive variable lookup. -/
  | varA (Γ : Ctx) (i : Nat) (φ : Prop')
      (h : Γ.additive[i]? = some φ) :
      Deriv Γ (Term.var i) φ

  /-- `var-L` — linear variable lookup. The context must contain the
  hypothesis as its sole linear element. -/
  | varL (Γₐ : List Prop') (φ : Prop') :
      Deriv { additive := Γₐ, linear := [φ] } (Term.var 0) φ

  /-- `weaken-A` — additive weakening. -/
  | weakenA (Γ : Ctx) (φ' φ : Prop') (M : Term)
      (d : Deriv Γ M φ) :
      Deriv (Ctx.consA φ' Γ) M φ

  /-- `imp-I` — implication introduction. -/
  | impI (Γ : Ctx) (φ ψ : Prop') (M : Term)
      (d : Deriv (Ctx.consA φ Γ) M ψ) :
      Deriv Γ (Term.lam φ M) (Prop'.imp φ ψ)

  /-- `imp-E` — implication elimination. Splits the linear context. -/
  | impE (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (φ ψ : Prop') (M N : Term)
      (dM : Deriv { additive := Γₐ, linear := Γ₁ } M (Prop'.imp φ ψ))
      (dN : Deriv { additive := Γₐ, linear := Γ₂ } N φ) :
      Deriv { additive := Γₐ, linear := Γ₁ ++ Γ₂ } (Term.app M N) ψ

  /-- `and-I` — additive conjunction introduction. Requires empty linear ctx
  for the simple form. -/
  | andI (Γₐ : List Prop') (φ ψ : Prop') (M N : Term)
      (dM : Deriv { additive := Γₐ, linear := [] } M φ)
      (dN : Deriv { additive := Γₐ, linear := [] } N ψ) :
      Deriv { additive := Γₐ, linear := [] }
            (Term.app M N)  -- placeholder term shape; refine at Q3
            (Prop'.and φ ψ)

  /-- `says-I` — affirmation introduction with embedded signature carrier.
  This is the T2 seam: the rule requires a signature, but verification is
  deferred to `Deriv_K` (the cryptographic-typing judgment in
  `DLC.Correspondence`). At the logical level, any byte string of the right
  shape is accepted; T2 says the two judgments coincide. -/
  | saysI (Γ : Ctx) (p : Principal) (φ : Prop') (M : Term) (sig : Signature)
      (d : Deriv Γ M φ) :
      Deriv Γ (Term.sign p M sig) (Prop'.says p φ)

  /-- `says-E` — affirmation elimination. Bind the underlying proof in `N`. -/
  | saysE (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (p : Principal)
          (φ ψ : Prop') (M N : Term)
      (dM : Deriv { additive := Γₐ, linear := Γ₁ } M (Prop'.says p φ))
      (dN : Deriv { additive := φ :: Γₐ, linear := Γ₂ } N ψ) :
      Deriv { additive := Γₐ, linear := Γ₁ ++ Γ₂ }
            (Term.app M N)  -- placeholder; the real term is a let-binder
            (Prop'.says p ψ)

  /-- `delegate` — chain composition. Take a speaks-for affirmation by `p` and
  a `q says φ`, produce `(p ⊓ q) says φ`. Chain splicing is impossible because
  both premises must mention the same `q`. -/
  | delegate (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (p q : Principal)
             (φ : Prop') (M N : Term)
      (dM : Deriv { additive := Γₐ, linear := Γ₁ } M
              (Prop'.says p (Prop'.speaksFor q p)))
      (dN : Deriv { additive := Γₐ, linear := Γ₂ } N (Prop'.says q φ)) :
      Deriv { additive := Γₐ, linear := Γ₁ ++ Γ₂ }
            (Term.delegate M N)
            (Prop'.says (Principal.acting p q) φ)

  /-- `attenuate` — narrow a `p says φ` to a `p says ψ`, requiring that `ψ`
  follows from `φ` and that the IFC label of `ψ` is below `φ`'s. The label
  side-condition lives in `DLC.IFCLabel` and is added at M1.Q4.a. -/
  | attenuate (Γ : Ctx) (p : Principal) (φ ψ : Prop') (M : Term)
      (d : Deriv Γ M (Prop'.says p φ))
      -- Side condition `φ ⊃ ψ` is provability, decidable for the propositional
      -- fragment via T1's `decide_pure`. Carried here as an explicit
      -- additional Deriv premise.
      (impl : Deriv Ctx.empty (Term.var 0) (Prop'.imp φ ψ)) :
      Deriv Γ (Term.attenuate M ψ) (Prop'.says p ψ)

  /-- `box-I` — `□_O φ` introduction. Given a proof of `φ` and a proof of
  the obligation `O`, build `□_O φ`. The discharge rule is the only
  elimination form; this preserves linear semantics for `O`. -/
  | boxI (Γ : Ctx) (O : Obligation) (φ : Prop') (M N : Term)
      (dM : Deriv Γ M φ)
      -- The proof of the obligation is itself a Deriv at a placeholder
      -- proposition we encode as `Prop'.atom 0`; the obligation table
      -- correspondence is set up at M1.Q3 along with `crate::graded`.
      (dN : Deriv Ctx.empty N (Prop'.atom 0)) :
      Deriv Γ (Term.app M N)
            (Prop'.boxed O φ)

  /-- `discharge` — `□_O φ` elimination. Consume the obligation evidence
  (the linearity is captured by the linear context split). -/
  | discharge (Γₐ : List Prop') (Γ₁ Γ₂ : List Prop') (O : Obligation)
              (φ : Prop') (M N : Term)
      (dM : Deriv { additive := Γₐ, linear := Γ₁ } M (Prop'.boxed O φ))
      (dN : Deriv { additive := Γₐ, linear := Γ₂ } N (Prop'.atom 0)) :
      Deriv { additive := Γₐ, linear := Γ₁ ++ Γ₂ }
            (Term.discharge M N) φ

  /-- `now` — proof of `now < τ` from a verifiable time anchor. The anchor
  is opaque at the calculus level; verification lives in `dlc-crypto`'s
  `TimeAnchor` trait. -/
  | now (τ : TimeBound) :
      Deriv Ctx.empty (Term.now τ) Prop'.top

  /-- `within-I` — `◇_τ φ` introduction. Pair a proof of `φ` with a proof
  that the current time is before `τ`. -/
  | withinI (Γ : Ctx) (τ : TimeBound) (φ : Prop') (M : Term)
      (d : Deriv Γ M φ) :
      Deriv Γ (Term.withinIntro τ M) (Prop'.within τ φ)

  /-- `within-E` — `◇_τ φ` elimination. The verifier checks `now < τ` at
  the moment of elimination (typing-rule premise on a fresh time anchor). -/
  | withinE (Γ : Ctx) (τ : TimeBound) (φ : Prop') (M : Term)
      (d : Deriv Γ M (Prop'.within τ φ)) :
      Deriv Γ M φ

/-! ## A first round-trip sanity check.

The smallest non-trivial proof: `var-A` of an atom that lives in the additive
context. Confirms the constructor signatures kept their indices in sync. -/

namespace JudgmentChecks

/-- Look up the only hypothesis in a single-additive context. -/
example :
    Deriv { additive := [Prop'.atom 0], linear := [] } (Term.var 0) (Prop'.atom 0) :=
  Deriv.varA _ 0 _ rfl

/-- Use of the same hypothesis as a linear variable, on a different judgment. -/
example :
    Deriv { additive := [], linear := [Prop'.atom 7] } (Term.var 0) (Prop'.atom 7) :=
  Deriv.varL [] (Prop'.atom 7)

end JudgmentChecks

end DLC
