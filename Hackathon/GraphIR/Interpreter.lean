import Hackathon.GraphIR.Builtins

/-!
# GraphIR — interpreter

A fueled, untyped, eager interpreter. The fuel parameter is the
recursion depth budget; every reduction step (including each call)
consumes one unit. Returning `none` means "stuck" — wrong types,
missing variable, unknown function, or out of fuel.

The interpreter is intentionally simple: a `match` over `Expr` cases
plus an environment of `(name, Val)` pairs. The user-defined function
bundle is consulted whenever `call f args` doesn't hit a built-in.
-/

namespace Hackathon.GraphIR

abbrev Env (V : Type) := List (String × Val V)

/-- Look up a variable. -/
def Env.get? {V : Type} (env : Env V) (name : String) : Option (Val V) :=
  match env with
  | [] => none
  | (n, v) :: rest => if n == name then some v else Env.get? rest name

/-- Bind a variable. -/
def Env.set {V : Type} (env : Env V) (name : String) (v : Val V) : Env V :=
  (name, v) :: env

/-- Convert a `Fin _`-sourced numeric literal into a `Val V`, when
    `V` happens to be `Fin n`. We expose this via the optional
    `vertOfNat` field of the runtime config. -/
abbrev VertCoerce (V : Type) := Nat → Option V

/-- Per-run interpreter configuration: ambient context + a way to
    convert numeric vertex literals into the chosen vertex type. -/
structure Config (V : Type) where
  ctx : Context V
  /-- How to interpret `vertLit i`. For `V = Fin n`, set this to
      `fun i => if h : i < n then some ⟨i, h⟩ else none`. -/
  vertOfNat : VertCoerce V := fun _ => none

namespace Interp

variable {V : Type} [DecidableEq V]

/-- Map a function returning `Option` over a list, threading the
    optionality. Public so unfolding lemmas can reference it. -/
def mapM_opt {α β : Type} (f : α → Option β) : List α → Option (List β)
  | []      => some []
  | x :: xs =>
      match f x with
      | none => none
      | some y =>
        match mapM_opt f xs with
        | none => none
        | some ys => some (y :: ys)

/-- Find a function by name. Public so unfolding lemmas can reference it. -/
def findFun (funs : List FunDecl) (name : String) : Option FunDecl :=
  funs.find? (fun f => f.name == name)

/-- The interpreter. Returns `none` on failure or fuel exhaustion. -/
def eval (cfg : Config V) (funs : List FunDecl) :
    Nat → Env V → Expr → Option (Val V)
  | 0, _, _ => none -- out of fuel
  | fuel+1, env, e =>
    match e with
    | .var x => env.get? x
    | .natLit n => some (.nat n)
    | .boolLit b => some (.bool b)
    | .vertLit i => (cfg.vertOfNat i).map .vert
    | .nilE => some (.list [])
    | .noneE => some (.opt none)
    | .letE x bound body =>
        match eval cfg funs fuel env bound with
        | none => none
        | some v => eval cfg funs fuel (env.set x v) body
    | .ite c thn els =>
        match eval cfg funs fuel env c with
        | some (.bool true) => eval cfg funs fuel env thn
        | some (.bool false) => eval cfg funs fuel env els
        | _ => none
    | .matchOpt scrut onN x onS =>
        match eval cfg funs fuel env scrut with
        | some (.opt none) => eval cfg funs fuel env onN
        | some (.opt (some v)) =>
            eval cfg funs fuel (env.set x v) onS
        | _ => none
    | .matchList scrut onN h t onC =>
        match eval cfg funs fuel env scrut with
        | some (.list []) => eval cfg funs fuel env onN
        | some (.list (a :: rest)) =>
            eval cfg funs fuel ((env.set h a).set t (.list rest)) onC
        | _ => none
    | .matchPair scrut a b body =>
        match eval cfg funs fuel env scrut with
        | some (.pair va vb) =>
            eval cfg funs fuel ((env.set a va).set b vb) body
        | _ => none
    | .call name args =>
        match mapM_opt (eval cfg funs fuel env) args with
        | none => none
        | some argVals =>
            -- built-in?
            match Builtin.eval cfg.ctx name argVals with
            | some r => some r
            | none =>
              -- user-defined?
              match findFun funs name with
              | none => none
              | some ⟨_, params, body⟩ =>
                  if params.length ≠ argVals.length then none
                  else
                    let env' := List.foldl (init := ([] : Env V))
                      (fun e (kv : String × Val V) => Env.set e kv.1 kv.2)
                      ((params.zip argVals).reverse)
                    eval cfg funs fuel env' body

/-- Run a `Program` with the given fuel and runtime config. -/
def run (cfg : Config V) (fuel : Nat) (p : Program) : Option (Val V) :=
  eval cfg p.funs fuel [] p.main

end Interp

/-! ## Convenience: vertex coercer for `Fin n` -/

namespace Config

/-- For `V = Fin n`, the natural numeric-vertex coercer. -/
def finVertOfNat (n : Nat) : VertCoerce (Fin n) :=
  fun i => if h : i < n then some ⟨i, h⟩ else none

end Config

end Hackathon.GraphIR
