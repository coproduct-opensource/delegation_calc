/-
DLC — Progress for the closed computational core (rung 3b-0).

T3's two-run design (`spec/t3-two-run-design-2026-07.md`, FINDING
2026-07-02) requires the computational core to satisfy progress: a
closed, well-typed core term is a value or takes a `step`. Before the
CONGRUENCE rules landed in `Reduce.lean`, nested eliminations were
stuck (`π₁ (π₁ ⟨⟨a,b⟩,c⟩)` had no reduct) and this theorem was false;
it is rung 3b-0's witness that the ξ-rules restore it.

"Computational core" (`spec/typing-rules.md` §11 'Values
(computational core)') excludes the four FROZEN eliminations — verify,
attenuate, declassify, discharge — which are checked by the verifier
layers rather than computed. `CoreTerm` gates them out syntactically;
`Value` is the set of call-by-name introduction forms (subterms
unevaluated).
-/

import DLC.Decidability
import DLC.Reduce

namespace DLC

/-- Computational-core terms: no frozen eliminations anywhere.
Frozen: verify, attenuate, declassify, discharge (no recursion into
them needed — one occurrence disqualifies the whole term). Everything
else recurses into all `Term` subterms; `var` and `now` are core
leaves. -/
def CoreTerm : Term → Bool
  | Term.var _ => true
  | Term.lam _ body => CoreTerm body
  | Term.app f x => CoreTerm f && CoreTerm x
  | Term.sign _ m _ => CoreTerm m
  | Term.verify _ _ _ => false
  | Term.delegate m n => CoreTerm m && CoreTerm n
  | Term.attenuate _ _ => false
  | Term.boxed _ _ _ => false
  | Term.discharge _ _ => false
  | Term.liftLabel _ m => CoreTerm m
  | Term.declassify _ _ _ => false
  | Term.now _ => true
  | Term.withinIntro _ m => CoreTerm m
  | Term.pair a b => CoreTerm a && CoreTerm b
  | Term.fst a => CoreTerm a
  | Term.snd a => CoreTerm a
  | Term.inl _ a => CoreTerm a
  | Term.inr _ a => CoreTerm a
  | Term.case s l r => CoreTerm s && CoreTerm l && CoreTerm r
  | Term.tensorIntro a b => CoreTerm a && CoreTerm b
  | Term.letTensor s b => CoreTerm s && CoreTerm b
  | Term.saysBind _ s b => CoreTerm s && CoreTerm b
  | Term.letSays _ s b => CoreTerm s && CoreTerm b
  | Term.sfExtract m => CoreTerm m

/-- Values of the core: introduction forms (call-by-name — subterms
unevaluated). -/
def Value : Term → Prop
  | Term.lam _ _ => True
  | Term.sign _ _ _ => True
  | Term.pair _ _ => True
  | Term.inl _ _ => True
  | Term.inr _ _ => True
  | Term.tensorIntro _ _ => True
  | Term.now _ => True
  | Term.withinIntro _ _ => True
  | Term.liftLabel _ _ => True
  | _ => False

/-! ## ξ-witnesses.

One lemma per elimination form: a stepping scrutinee/function position
yields a step of the whole form. Each proof cases on the scrutinee's
shape — values and frozen forms refute the hypothesis (their `step` is
`none`), head-redex shapes step outright, and everything else falls
through to the congruence branch of `step` (unfold both the hypothesis
and the goal one layer, then rewrite). -/

private theorem app_steps {f f' : Term} (x : Term)
    (hf : step f = some f') : ∃ r, step (Term.app f x) = some r := by
  cases f <;>
    first
      | (simp [step] at hf; done)
      | (refine ⟨Term.app f' x, ?_⟩
         simp only [step] at hf ⊢
         rw [hf])

private theorem fst_steps {m m' : Term}
    (hm : step m = some m') : ∃ r, step (Term.fst m) = some r := by
  cases m <;>
    first
      | (simp [step] at hm; done)
      | (refine ⟨Term.fst m', ?_⟩
         simp only [step] at hm ⊢
         rw [hm])

private theorem snd_steps {m m' : Term}
    (hm : step m = some m') : ∃ r, step (Term.snd m) = some r := by
  cases m <;>
    first
      | (simp [step] at hm; done)
      | (refine ⟨Term.snd m', ?_⟩
         simp only [step] at hm ⊢
         rw [hm])

private theorem case_steps {s s' : Term} (l r : Term)
    (hs : step s = some s') : ∃ t, step (Term.case s l r) = some t := by
  cases s <;>
    first
      | (simp [step] at hs; done)
      | (refine ⟨Term.case s' l r, ?_⟩
         simp only [step] at hs ⊢
         rw [hs])

private theorem letTensor_steps {s s' : Term} (b : Term)
    (hs : step s = some s') : ∃ t, step (Term.letTensor s b) = some t := by
  cases s <;>
    first
      | (simp [step] at hs; done)
      | (refine ⟨Term.letTensor s' b, ?_⟩
         simp only [step] at hs ⊢
         rw [hs])

private theorem letSays_steps {s s' : Term} (p : Principal) (b : Term)
    (hs : step s = some s') : ∃ t, step (Term.letSays p s b) = some t := by
  cases s <;>
    first
      | (simp [step] at hs; done)
      | (refine ⟨Term.letSays p s' b, ?_⟩
         simp only [step] at hs ⊢
         rw [hs])

private theorem sfExtract_steps {m m' : Term}
    (hm : step m = some m') : ∃ r, step (Term.sfExtract m) = some r := by
  cases m <;>
    first
      | (simp [step] at hm; done)
      | (refine ⟨Term.sfExtract m', ?_⟩
         simp only [step] at hm ⊢
         rw [hm])

private theorem delegate_left_steps {m m' : Term} (n : Term)
    (hm : step m = some m') : ∃ t, step (Term.delegate m n) = some t := by
  cases m <;>
    first
      | (simp [step] at hm; done)
      | (refine ⟨Term.delegate m' n, ?_⟩
         simp only [step] at hm ⊢
         rw [hm])

private theorem delegate_right_steps {n n' : Term} (p : Principal)
    (mi : Term) (si : Signature) (hn : step n = some n') :
    ∃ t, step (Term.delegate (Term.sign p mi si) n) = some t := by
  cases n <;>
    first
      | (simp [step] at hn; done)
      | (refine ⟨Term.delegate (Term.sign p mi si) n', ?_⟩
         simp only [step] at hn ⊢
         rw [hn])

/-! ## Progress. -/

/-- Auxiliary form with the context generalized (Lean's `induction`
needs the `[]` index to be a variable). Induction on the derivation:
introduction forms are values; frozen eliminations are excluded by
`CoreTerm`; for each computational elimination, the scrutinee IH
either yields a step (a ξ-witness lemma lifts it to the whole form) or
a value, whose canonical form — forced by syntax-directed inversion of
the scrutinee's derivation — fires the head redex. -/
private theorem progress_aux {Γ : List Prop'} {M : Term} {φ : Prop'}
    (d : PropDeriv Γ M φ) :
    Γ = [] → CoreTerm M = true → Value M ∨ ∃ M', step M = some M' := by
  induction d with
  | varA _ i _ hlk =>
    -- No variables in the empty context.
    intro hΓ _
    subst hΓ
    simp at hlk
  | impI _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | impE Γ α β f x dM dN ihM _ =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm, Bool.and_eq_true] at hcore
    rcases ihM rfl hcore.1 with hval | ⟨f', hstep⟩
    · -- Canonical forms: a value of type α ⊃ β must be a lam — β fires.
      cases f with
      | lam _ body => exact Or.inr ⟨_, rfl⟩
      | _ => first
          | exact False.elim hval
          | cases dM
    · exact Or.inr (app_steps x hstep)
  | saysI _ _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | verifyE _ _ _ _ _ _ _ =>
    -- verify is frozen: not a core term.
    intro _ hcore; simp [CoreTerm] at hcore
  | andI _ _ _ _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | andEL Γ α β a dA ihA =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm] at hcore
    rcases ihA rfl hcore with hval | ⟨a', hstep⟩
    · -- A value of type α ∧ β must be a pair — π₁ fires.
      cases a with
      | pair u v => exact Or.inr ⟨u, rfl⟩
      | _ => first
          | exact False.elim hval
          | cases dA
    · exact Or.inr (fst_steps hstep)
  | andER Γ α β a dA ihA =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm] at hcore
    rcases ihA rfl hcore with hval | ⟨a', hstep⟩
    · cases a with
      | pair u v => exact Or.inr ⟨v, rfl⟩
      | _ => first
          | exact False.elim hval
          | cases dA
    · exact Or.inr (snd_steps hstep)
  | withinI _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | orI_L _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | orI_R _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | tensorI _ _ _ _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | orE Γ α β χ S L R dS dL dR ihS _ _ =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm, Bool.and_eq_true] at hcore
    rcases ihS rfl hcore.1.1 with hval | ⟨S', hstep⟩
    · -- A value of type α ∨ β must be an injection — case-β fires.
      cases S with
      | inl _ a => exact Or.inr ⟨_, rfl⟩
      | inr _ a => exact Or.inr ⟨_, rfl⟩
      | _ => first
          | exact False.elim hval
          | cases dS
    · exact Or.inr (case_steps L R hstep)
  | letSaysE Γ p α β S B dS dB ihS _ =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm, Bool.and_eq_true] at hcore
    rcases ihS rfl hcore.1 with hval | ⟨S', hstep⟩
    · -- A value of type p says α must be a sign, and inversion forces
      -- its principal to be p — the `if p = p'` guard passes.
      cases S with
      | sign p' m sig =>
        cases dS with
        | saysI _ _ _ _ _ _ => exact Or.inr ⟨subst B m, by simp [step]⟩
      | _ => first
          | exact False.elim hval
          | cases dS
    · exact Or.inr (letSays_steps p B hstep)
  | sfExtractE Γ p q m dM ihM =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm] at hcore
    rcases ihM rfl hcore with hval | ⟨m', hstep⟩
    · -- A value of type p says (q ⇒ p) must be a sign — extract fires.
      cases m with
      | sign _ inner _ => exact Or.inr ⟨inner, rfl⟩
      | _ => first
          | exact False.elim hval
          | cases dM
    · exact Or.inr (sfExtract_steps hstep)
  | delegate Γ p q α m n dM dN ihM ihN =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm, Bool.and_eq_true] at hcore
    rcases ihM rfl hcore.1 with hvalM | ⟨m', hstepM⟩
    · -- Left is a value of type p says (q ⇒ p) — a sign. Then the
      -- right position: value → sign → delegate-β; else ξ-right.
      cases m with
      | sign pm mi si =>
        rcases ihN rfl hcore.2 with hvalN | ⟨n', hstepN⟩
        · cases n with
          | sign _ ni s' => exact Or.inr ⟨_, rfl⟩
          | _ => first
              | exact False.elim hvalN
              | cases dN
        · exact Or.inr (delegate_right_steps pm mi si hstepN)
      | _ => first
          | exact False.elim hvalM
          | cases dM
    · exact Or.inr (delegate_left_steps n hstepM)
  | now _ _ => intro _ _; exact Or.inl True.intro
  | attenuate _ _ _ _ _ _ =>
    intro _ hcore; simp [CoreTerm] at hcore
  | liftLabel _ _ _ _ _ _ => intro _ _; exact Or.inl True.intro
  | declassify _ _ _ _ _ _ _ _ _ _ =>
    intro _ hcore; simp [CoreTerm] at hcore
  | discharge _ _ _ _ _ _ _ _ _ =>
    intro _ hcore; simp [CoreTerm] at hcore
  | letTensor Γ α β χ S B dS dB ihS _ =>
    intro hΓ hcore
    subst hΓ
    simp only [CoreTerm, Bool.and_eq_true] at hcore
    rcases ihS rfl hcore.1 with hval | ⟨S', hstep⟩
    · -- A value of type α ⊗ β must be a tensorIntro — let-tensor-β fires.
      cases S with
      | tensorIntro a b => exact Or.inr ⟨_, rfl⟩
      | _ => first
          | exact False.elim hval
          | cases dS
    · exact Or.inr (letTensor_steps B hstep)

/-- Progress for the closed computational core: a closed, well-typed
core term is a value or takes a `step`. Rung 3b-0's witness that the
congruence rules un-stick nested eliminations. -/
theorem progress {M : Term} {φ : Prop'}
    (d : PropDeriv [] M φ) (hcore : CoreTerm M = true) :
    Value M ∨ ∃ M', step M = some M' :=
  progress_aux d rfl hcore

end DLC
