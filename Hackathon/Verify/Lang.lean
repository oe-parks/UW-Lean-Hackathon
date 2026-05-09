import Mathlib.Tactic

/-!
# A small imperative language (IMP)

This is the **language layer** of the verification framework.

* `Vname` — variable names (strings).
* `State` — total maps from variable names to integers.
* `AExp` / `BExp` — arithmetic and boolean expressions.
* `Com` — commands: skip, assignment, sequencing, if, while.

Programs over this AST are verified in `Hackathon/Verify/Hoare.lean`
against specifications written as Lean predicates over `State`.
-/

namespace Hackathon.Verify

abbrev Vname := String
abbrev State := Vname → Int

/-- Functional state update: `update s x v` rebinds `x` to `v`. -/
def update (s : State) (x : Vname) (v : Int) : State :=
  fun y => if y = x then v else s y

@[simp] theorem update_eq (s : State) (x : Vname) (v : Int) :
    update s x v x = v := by
  unfold update; simp

@[simp] theorem update_neq (s : State) (x y : Vname) (v : Int) (h : y ≠ x) :
    update s x v y = s y := by
  unfold update; simp [h]

/-- Arithmetic expressions. -/
inductive AExp where
  | num : Int → AExp
  | var : Vname → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
deriving Repr

namespace AExp

def eval : AExp → State → Int
  | num n,   _ => n
  | var x,   s => s x
  | add a b, s => eval a s + eval b s
  | sub a b, s => eval a s - eval b s
  | mul a b, s => eval a s * eval b s

end AExp

/-- Boolean expressions. -/
inductive BExp where
  | tt  : BExp
  | ff  : BExp
  | not : BExp → BExp
  | and : BExp → BExp → BExp
  | eq  : AExp → AExp → BExp
  | lt  : AExp → AExp → BExp
  | le  : AExp → AExp → BExp
deriving Repr

namespace BExp

def eval : BExp → State → Bool
  | tt,        _ => true
  | ff,        _ => false
  | not b,     s => !eval b s
  | and b₁ b₂, s => eval b₁ s && eval b₂ s
  | eq a₁ a₂,  s => decide (a₁.eval s = a₂.eval s)
  | lt a₁ a₂,  s => decide (a₁.eval s < a₂.eval s)
  | le a₁ a₂,  s => decide (a₁.eval s ≤ a₂.eval s)

end BExp

/-- Commands of the IMP language. -/
inductive Com where
  | skip   : Com
  | assign : Vname → AExp → Com
  | seq    : Com → Com → Com
  | ifte   : BExp → Com → Com → Com
  | while_ : BExp → Com → Com
deriving Repr

end Hackathon.Verify
