import DlcCore
import DLC.Syntax
import DLC.Principal
import DLC.Obligation
import DLC.Time
import DLC.IFCLabel
import DLC.Judgment

/-!
# Concrete decode: Aeneas `dlc_core.*` → hand `DLC.*`

Stage 1a of the `infer_square` transport (`spec/r6.2-inc1-infer-square-design.md` §1a): the
concrete, total, computable, structural decode from the Aeneas-generated `dlc_core` AST
(`syntax.Term` / `syntax.Prop` / `judgment.Ctx` …) to the hand `DLC` AST. It is what lets
`decideLean`'s soundness (about a hand `Deriv`) be composed with the shipped Rust checker
`decide.infer` to yield `rust_decide_sound` — the verified certificate checker.

**1:1 on the faithful constructors.** Labels (`ifc.Label = Vec U32`) and DP-budget obligations
decode to a **total default** (`DLC.Label.bottom` / `DLC.Obligation.top`): a faithful
`Vec U32 → CapabilityLattice` decode is impossible (established at `lean/DLCD/Transport.lean`), and
it is sound here because every label-or-dpbudget-carrying constructor is **fail-closed in
`decideLean`** — the checker never inspects one, so a total decode suffices.
-/

namespace DLC.DecideDecode

open Aeneas Aeneas.Std Result
open dlc_core

/-- Labels: total default (checker-fail-closed; faithful decode impossible). -/
def decLabel (_ : ifc.Label) : DLC.Label := DLC.Label.bottom

/-- `TimeBound`: `U64 → Nat`. -/
def decTimeBound (t : time.TimeBound) : DLC.TimeBound := ⟨t.epoch_ms.val⟩

/-- `Signature`: `U8 → UInt8` on `alg`; `Vec U8 → List UInt8` on `bytes`. -/
def decSignature (s : syntax.Signature) : DLC.Signature :=
  ⟨UInt8.ofNat s.alg.val, s.bytes.val.map (fun b => UInt8.ofNat b.val)⟩

/-- `PrincipalId`: `Array U8 32 → List UInt8`. -/
def decPrincipalId (a : principal.PrincipalId) : DLC.PrincipalId :=
  ⟨a.val.map (fun b => UInt8.ofNat b.val)⟩

/-- `ActionId`: `Vec U8 → List UInt8`. -/
def decActionId (a : obligation.ActionId) : DLC.ActionId :=
  ⟨a.val.map (fun b => UInt8.ofNat b.val)⟩

/-- `Principal`: structural 1:1. -/
def decPrincipal : principal.Principal → DLC.Principal
  | .Atom pid => .atom (decPrincipalId pid)
  | .And a b => .and (decPrincipal a) (decPrincipal b)
  | .Or a b => .or (decPrincipal a) (decPrincipal b)
  | .Acting a b => .acting (decPrincipal a) (decPrincipal b)

/-- `Obligation`: structural; `DpBudget` → total default `.top` (checker-fail-closed). -/
def decObligation : obligation.Obligation → DLC.Obligation
  | .Top => .top
  | .Bot => .bot
  | .ActOf p a => .actOf (decPrincipal p) (decActionId a)
  | .Within t => .within (decTimeBound t)
  | .Tensor a b => .tensor (decObligation a) (decObligation b)
  | .Lolli a b => .lolli (decObligation a) (decObligation b)
  | .DpBudget _ => .top

/-- `Prop`: structural 1:1 (`Atom U32 → atom Nat`; labels via `decLabel`). -/
def decProp : syntax.Prop → DLC.Prop'
  | .Top => .top
  | .Bot => .bot
  | .Atom i => .atom i.val
  | .Imp a b => .imp (decProp a) (decProp b)
  | .And a b => .and (decProp a) (decProp b)
  | .Or a b => .or (decProp a) (decProp b)
  | .Says p f => .says (decPrincipal p) (decProp f)
  | .SpeaksFor p q => .speaksFor (decPrincipal p) (decPrincipal q)
  | .At f l => .at (decProp f) (decLabel l)
  | .Boxed o f => .boxed (decObligation o) (decProp f)
  | .Within t f => .within (decTimeBound t) (decProp f)
  | .Tensor a b => .tensor (decProp a) (decProp b)
  | .Lolli a b => .lolli (decProp a) (decProp b)
  | .Replicated f l => .replicated (decProp f) (decLabel l)

/-- `Term`: structural 1:1 across all 26 constructors (`Var U32 → var Nat`). -/
def decTerm : syntax.Term → DLC.Term
  | .Var i => .var i.val
  | .Lam f b => .lam (decProp f) (decTerm b)
  | .App f x => .app (decTerm f) (decTerm x)
  | .Sign p m sig => .sign (decPrincipal p) (decTerm m) (decSignature sig)
  | .Verify p m sig => .verify (decPrincipal p) (decTerm m) (decSignature sig)
  | .Delegate a b => .delegate (decTerm a) (decTerm b)
  | .Attenuate m f => .attenuate (decTerm m) (decProp f)
  | .SaysBind p m n => .saysBind (decPrincipal p) (decTerm m) (decTerm n)
  | .Boxed o m n => .boxed (decObligation o) (decTerm m) (decTerm n)
  | .Discharge a b => .discharge (decTerm a) (decTerm b)
  | .LiftLabel l m => .liftLabel (decLabel l) (decTerm m)
  | .Declassify l m n => .declassify (decLabel l) (decTerm m) (decTerm n)
  | .Now t => .now (decTimeBound t)
  | .WithinIntro t m => .withinIntro (decTimeBound t) (decTerm m)
  | .Pair a b => .pair (decTerm a) (decTerm b)
  | .Fst a => .fst (decTerm a)
  | .Snd a => .snd (decTerm a)
  | .Inl f m => .inl (decProp f) (decTerm m)
  | .Inr f m => .inr (decProp f) (decTerm m)
  | .Case s l r => .case (decTerm s) (decTerm l) (decTerm r)
  | .TensorIntro a b => .tensorIntro (decTerm a) (decTerm b)
  | .LetTensor a b => .letTensor (decTerm a) (decTerm b)
  | .LetSays p a b => .letSays (decPrincipal p) (decTerm a) (decTerm b)
  | .SfExtract m => .sfExtract (decTerm m)
  | .Command a b l => .command (decTerm a) (decTerm b) (decLabel l)
  | .RunCmd a b => .runCmd (decTerm a) (decTerm b)

/-- `Ctx`: pointwise `decProp` over the additive and linear `Vec`s. -/
def decCtx (c : judgment.Ctx) : DLC.Ctx :=
  ⟨c.additive.val.map decProp, c.linear.val.map decProp⟩

end DLC.DecideDecode
