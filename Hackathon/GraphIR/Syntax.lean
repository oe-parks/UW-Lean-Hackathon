import Hackathon.GraphIR.Types

/-!
# GraphIR — syntax

Functional / SSA-style — every binding is a `let`, no mutation. Variables
are looked up in an environment (string keys). Recursion is via top-level
`FunDecl`s; `call f args` invokes either a built-in or a user function.

Pattern matching has *destructor-style* eliminators (`matchOpt`,
`matchList`, `matchPair`) rather than a generic match — keeps the AST
small and the interpreter trivial.
-/

namespace Hackathon.GraphIR

/-- IR expressions. Untyped; type errors become interpreter `none`s. -/
inductive Expr : Type where
  /-- Variable lookup. -/
  | var (name : String) : Expr
  /-- Literal `Nat`. -/
  | natLit (n : Nat) : Expr
  /-- Literal `Bool`. -/
  | boolLit (b : Bool) : Expr
  /-- Literal vertex (by `.val`, when the vertex type is `Fin n`). -/
  | vertLit (i : Nat) : Expr
  /-- Empty list. -/
  | nilE : Expr
  /-- Empty option (`none`). -/
  | noneE : Expr
  /-- `let name := bound in body` — the SSA spine. -/
  | letE (name : String) (bound body : Expr) : Expr
  /-- `if cond then thn else els`. -/
  | ite (cond thn els : Expr) : Expr
  /-- Eliminator for `Option`: `match scrut with | none => onN | some x => onS x`. -/
  | matchOpt (scrut onN : Expr) (x : String) (onS : Expr) : Expr
  /-- Eliminator for lists: `match scrut with | [] => onN | h::t => onC h t`. -/
  | matchList (scrut onN : Expr) (h t : String) (onC : Expr) : Expr
  /-- Eliminator for pairs: `match scrut with | (a, b) => body`. -/
  | matchPair (scrut : Expr) (a b : String) (body : Expr) : Expr
  /-- Built-in or user-defined call. -/
  | call (name : String) (args : List Expr) : Expr
  deriving Repr, Inhabited

/-- A user-defined IR function. -/
structure FunDecl where
  name : String
  params : List String
  body : Expr
  deriving Repr, Inhabited

/-- A complete IR program: mutually recursive function bundle + main. -/
structure Program where
  funs : List FunDecl
  main : Expr
  deriving Repr, Inhabited

end Hackathon.GraphIR
