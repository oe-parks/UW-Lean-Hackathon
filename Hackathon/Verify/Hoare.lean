import Hackathon.Verify.Semantics

/-!
# Hoare logic — the specification & verification layer

A specification is a triple `{P} c {Q}` (`HoareTriple P c Q`):
*if* the program `c` is run from a state satisfying `P` *and* it
terminates in state `s'`, *then* `Q s'` holds. This is the standard
**partial-correctness** Hoare interpretation.

The verifier is the rule system below: each rule is a Lean theorem
proven sound against the big-step semantics. To verify a program, the
user constructs a derivation (i.e. a Lean proof term) using only these
rules — by soundness, the resulting triple is true.
-/

namespace Hackathon.Verify

/-- Assertions are predicates over states. -/
abbrev Assn := State → Prop

/-- Partial-correctness Hoare triple. -/
def HoareTriple (P : Assn) (c : Com) (Q : Assn) : Prop :=
  ∀ ⦃s s' : State⦄, P s → BigStep c s s' → Q s'

namespace HoareTriple

/-! ### Sound inference rules -/

/-- `{P} skip {P}`. -/
theorem skip {P : Assn} : HoareTriple P .skip P := by
  intro s s' hP h
  cases h
  exact hP

/-- `{Q[a/x]} x := a {Q}` — backward assignment rule. -/
theorem assign (Q : Assn) (x : Vname) (a : AExp) :
    HoareTriple (fun s => Q (update s x (a.eval s))) (.assign x a) Q := by
  intro s s' hP h
  cases h
  exact hP

/-- Sequencing: glue two triples sharing a midpoint assertion. -/
theorem seq {P R Q : Assn} {c₁ c₂ : Com}
    (h₁ : HoareTriple P c₁ R) (h₂ : HoareTriple R c₂ Q) :
    HoareTriple P (.seq c₁ c₂) Q := by
  intro s s' hP hbig
  cases hbig with
  | seq h12 h23 => exact h₂ (h₁ hP h12) h23

/-- Conditional: prove the then- and else- branches under the matching
test outcome. -/
theorem ifte {P Q : Assn} {b : BExp} {c₁ c₂ : Com}
    (hT : HoareTriple (fun s => P s ∧ b.eval s = true) c₁ Q)
    (hF : HoareTriple (fun s => P s ∧ b.eval s = false) c₂ Q) :
    HoareTriple P (.ifte b c₁ c₂) Q := by
  intro s s' hP hbig
  cases hbig with
  | ifTrue  hb hc => exact hT ⟨hP, hb⟩ hc
  | ifFalse hb hc => exact hF ⟨hP, hb⟩ hc

/-- The workhorse helper for the `while` rule: an invariant `I`
preserved by the body is maintained across the whole loop, and on exit
the loop test is false.

Proven by induction on the big-step derivation, with the command
generalized so the inductive hypothesis stays usable. -/
private lemma while_aux {I : Assn} {b : BExp} {c : Com}
    (hbody : HoareTriple (fun s => I s ∧ b.eval s = true) c I) :
    ∀ {w : Com} {s s' : State},
      BigStep w s s' → w = .while_ b c → I s →
      I s' ∧ b.eval s' = false := by
  intro w s s' h
  induction h with
  | skip            => intro heq; cases heq
  | assign          => intro heq; cases heq
  | seq _ _         => intro heq; cases heq
  | ifTrue _ _      => intro heq; cases heq
  | ifFalse _ _     => intro heq; cases heq
  | whileFalse hb =>
      intro heq hI
      cases heq
      exact ⟨hI, hb⟩
  | whileTrue hb hcbody _ _ ihw =>
      intro heq hI
      cases heq
      exact ihw rfl (hbody ⟨hI, hb⟩ hcbody)

/-- `{I ∧ b} c {I}  ⊢  {I} while b do c {I ∧ ¬b}`. -/
theorem while_ {I : Assn} {b : BExp} {c : Com}
    (hbody : HoareTriple (fun s => I s ∧ b.eval s = true) c I) :
    HoareTriple I (.while_ b c) (fun s => I s ∧ b.eval s = false) := by
  intro s s' hI hbig
  exact while_aux hbody hbig rfl hI

/-- Rule of consequence: strengthen the precondition, weaken the
postcondition. -/
theorem consequence {P P' Q Q' : Assn} {c : Com}
    (hP : ∀ s, P s → P' s)
    (h : HoareTriple P' c Q')
    (hQ : ∀ s, Q' s → Q s) :
    HoareTriple P c Q := by
  intro s s' hPs hbig
  exact hQ s' (h (hP s hPs) hbig)

/-- Strengthen precondition only. -/
theorem consequence_left {P P' Q : Assn} {c : Com}
    (hP : ∀ s, P s → P' s) (h : HoareTriple P' c Q) :
    HoareTriple P c Q :=
  consequence hP h (fun _ q => q)

/-- Weaken postcondition only. -/
theorem consequence_right {P Q Q' : Assn} {c : Com}
    (h : HoareTriple P c Q') (hQ : ∀ s, Q' s → Q s) :
    HoareTriple P c Q :=
  consequence (fun _ p => p) h hQ

end HoareTriple

end Hackathon.Verify
