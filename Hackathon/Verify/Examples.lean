import Hackathon.Verify.Hoare

/-!
# Worked verifications

Each example builds a derivation in the Hoare-logic spec language using
the rules from `Hoare.lean`. Because every rule is sound against the
big-step semantics, the resulting `HoareTriple` is a real correctness
theorem about the program.
-/

namespace Hackathon.Verify

/-- `{True} x := 5 {x = 5}`. -/
example :
    HoareTriple (fun _ => True) (.assign "x" (.num 5))
                (fun s => s "x" = 5) := by
  apply HoareTriple.consequence_left _
    (HoareTriple.assign (fun s => s "x" = 5) "x" (.num 5))
  intro s _
  change update s "x" 5 "x" = 5
  exact update_eq _ _ _

/-- `{True} x := 1; y := 2 {x = 1 ∧ y = 2}`. -/
example :
    HoareTriple (fun _ => True)
      (.seq (.assign "x" (.num 1)) (.assign "y" (.num 2)))
      (fun s => s "x" = 1 ∧ s "y" = 2) := by
  -- First half: `{True} x := 1 {x = 1}`.
  have h₁ :
      HoareTriple (fun _ => True) (.assign "x" (.num 1))
                  (fun s => s "x" = 1) := by
    apply HoareTriple.consequence_left _
      (HoareTriple.assign (fun s => s "x" = 1) "x" (.num 1))
    intro s _
    change update s "x" 1 "x" = 1
    exact update_eq _ _ _
  -- Second half: `{x = 1} y := 2 {x = 1 ∧ y = 2}`.
  have h₂ :
      HoareTriple (fun s => s "x" = 1) (.assign "y" (.num 2))
                  (fun s => s "x" = 1 ∧ s "y" = 2) := by
    apply HoareTriple.consequence_left _
      (HoareTriple.assign (fun s => s "x" = 1 ∧ s "y" = 2) "y" (.num 2))
    intro s hx
    change update s "y" 2 "x" = 1 ∧ update s "y" 2 "y" = 2
    refine ⟨?_, ?_⟩
    · rw [update_neq _ "y" "x" 2 (by decide)]
      exact hx
    · exact update_eq _ _ _
  exact HoareTriple.seq h₁ h₂

/-- `{x = n ∧ n ≥ 0} while 0 < x do x := x - 1 {x = 0}`.

Demonstrates the while rule with invariant `0 ≤ s "x"`. -/
example (n : Int) (hn : 0 ≤ n) :
    HoareTriple (fun s => s "x" = n)
      (.while_ (.lt (.num 0) (.var "x"))
               (.assign "x" (.sub (.var "x") (.num 1))))
      (fun s => s "x" = 0) := by
  -- Body preserves the invariant `0 ≤ s "x"`.
  have hbody :
      HoareTriple
        (fun s => (0 ≤ s "x") ∧
                  (BExp.lt (.num 0) (.var "x")).eval s = true)
        (.assign "x" (.sub (.var "x") (.num 1)))
        (fun s => 0 ≤ s "x") := by
    apply HoareTriple.consequence_left _
      (HoareTriple.assign (fun s => 0 ≤ s "x") "x"
        (.sub (.var "x") (.num 1)))
    rintro s ⟨_, hb⟩
    have hb' : 0 < s "x" := by
      simpa [BExp.eval, AExp.eval] using hb
    change 0 ≤ update s "x" ((AExp.sub (.var "x") (.num 1)).eval s) "x"
    rw [update_eq]
    change 0 ≤ s "x" - 1
    omega
  -- Sandwich the while rule with consequence on both sides.
  refine HoareTriple.consequence ?_ (HoareTriple.while_ hbody) ?_
  · intro s heq
    change 0 ≤ s "x"
    rw [heq]; exact hn
  · rintro s ⟨hI, hb⟩
    have hb' : ¬ 0 < s "x" := by
      simpa [BExp.eval, AExp.eval] using hb
    change s "x" = 0
    omega

end Hackathon.Verify
