import Hackathon.Verify.Lang

/-!
# Big-step operational semantics

`BigStep c s s'` says: starting from state `s`, command `c` terminates
in state `s'`. This is the **meaning of programs** that the Hoare-logic
spec language is sound with respect to.
-/

namespace Hackathon.Verify

/-- Big-step evaluation relation. -/
inductive BigStep : Com → State → State → Prop where
  | skip {s} :
      BigStep .skip s s
  | assign {s x a} :
      BigStep (.assign x a) s (update s x (a.eval s))
  | seq {c₁ c₂ s s' s''} :
      BigStep c₁ s s' → BigStep c₂ s' s'' →
      BigStep (.seq c₁ c₂) s s''
  | ifTrue {b c₁ c₂ s s'} :
      b.eval s = true → BigStep c₁ s s' →
      BigStep (.ifte b c₁ c₂) s s'
  | ifFalse {b c₁ c₂ s s'} :
      b.eval s = false → BigStep c₂ s s' →
      BigStep (.ifte b c₁ c₂) s s'
  | whileFalse {b c s} :
      b.eval s = false →
      BigStep (.while_ b c) s s
  | whileTrue {b c s s' s''} :
      b.eval s = true → BigStep c s s' → BigStep (.while_ b c) s' s'' →
      BigStep (.while_ b c) s s''

end Hackathon.Verify
