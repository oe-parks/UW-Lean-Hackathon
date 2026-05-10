import Hackathon.Graph.Toy.Walk

/-!
# GraphIR — values

The IR is a small functional, untyped, deep-embedded language with a
fixed universe of *values*. Every value is one of:

* `nat`   — a natural number,
* `bool`  — a Boolean,
* `vert`  — a vertex of the underlying graph (parameterized by `V`),
* `list`  — a list of values,
* `pair`  — an ordered pair,
* `opt`   — an option (`none` / `some`).

Graphs and matchings are *not* values — they live in the runtime
`Context` (see `Interpreter.lean`). Programs reference the ambient graph
implicitly via primitive operations like `neighbors`.

This is the minimal universe to write BFS, matching, and other
graph-flavoured algorithms. It is also the right alphabet for a future
"data-structure GraphIR" lowering pass.
-/

namespace Hackathon.GraphIR

/-- IR values, parameterized by the vertex type.

    `graph` carries a vertex list and an edge list — a first-class
    graph value, distinct from the ambient `Context` graph. This lets
    IR functions accept a graph as an argument and (e.g.) contract
    a blossom to produce a smaller graph for a recursive call. -/
inductive Val (V : Type) : Type where
  | nat   : Nat → Val V
  | bool  : Bool → Val V
  | vert  : V → Val V
  | list  : List (Val V) → Val V
  | pair  : Val V → Val V → Val V
  | opt   : Option (Val V) → Val V
  | graph : List V → List (V × V) → Val V
  deriving Inhabited

namespace Val

/-- Decidable equality on `Val V`, given decidable equality on `V`. -/
def beq {V : Type} [DecidableEq V] : Val V → Val V → Bool
  | .nat n,   .nat m   => n == m
  | .bool a,  .bool b  => a == b
  | .vert u,  .vert v  => decide (u = v)
  | .list xs, .list ys =>
      let rec listEq : List (Val V) → List (Val V) → Bool
        | [], [] => true
        | x :: xs, y :: ys => beq x y && listEq xs ys
        | _, _ => false
      listEq xs ys
  | .pair a₁ b₁, .pair a₂ b₂ => beq a₁ a₂ && beq b₁ b₂
  | .opt none, .opt none => true
  | .opt (some x), .opt (some y) => beq x y
  | .graph vs₁ es₁, .graph vs₂ es₂ =>
      decide (vs₁ = vs₂) && decide (es₁ = es₂)
  | _, _ => false

instance {V : Type} [DecidableEq V] : BEq (Val V) where beq := beq

/-- Pretty-print. -/
partial def reprAux {V : Type} [Repr V] : Val V → Std.Format
  | .nat n   => Std.Format.text s!"{n}"
  | .bool b  => Std.Format.text (if b then "true" else "false")
  | .vert v  => Std.Format.text s!"v{repr v}"
  | .list xs =>
      let parts := xs.map reprAux
      Std.Format.bracket "[" (Std.Format.joinSep parts ", ") "]"
  | .pair a b =>
      Std.Format.bracket "(" (reprAux a ++ ", " ++ reprAux b) ")"
  | .opt none     => "none"
  | .opt (some x) => Std.Format.text "some " ++ reprAux x
  | .graph vs es  =>
      Std.Format.text s!"graph(|V|={vs.length}, |E|={es.length})"

instance {V : Type} [Repr V] : Repr (Val V) where
  reprPrec v _ := reprAux v

end Val

/-- Convenience constructors. -/
@[inline] def Val.true  {V : Type} : Val V := Val.bool .true
@[inline] def Val.false {V : Type} : Val V := Val.bool .false
@[inline] def Val.none' {V : Type} : Val V := Val.opt .none
@[inline] def Val.some' {V : Type} (v : Val V) : Val V := Val.opt (.some v)
@[inline] def Val.nil {V : Type} : Val V := Val.list []

end Hackathon.GraphIR
