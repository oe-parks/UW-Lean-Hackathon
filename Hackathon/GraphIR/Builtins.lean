import Hackathon.GraphIR.Syntax

/-!
# GraphIR — built-in operations

The IR's primitive operations live in a single dispatch table indexed by
the operation's name (a string). The interpreter calls
`evalBuiltin ctx name args` and gets back `Option (Val V)`.

Operations are partial: feeding wrong-shaped arguments returns `none`.
That keeps the IR untyped without giving up safety.

`Context V` carries the runtime "world": a vertex enumeration, the
adjacency relation as a decidable function, and (optionally) a matching.
-/

namespace Hackathon.GraphIR

/-- Runtime context for IR programs. -/
structure Context (V : Type) where
  /-- All vertices of the graph (used by `graph_vertices`, `neighbors`, …). -/
  vertices : List V
  /-- Adjacency as a decidable function. -/
  isAdj : V → V → Bool
  /-- Matching as a decidable symmetric relation; `false` for the empty matching. -/
  isMate : V → V → Bool

namespace Context

/-- Empty matching: nothing is matched. -/
@[inline] def emptyMate (V : Type) : V → V → Bool := fun _ _ => false

/-- Construct a context from a list of vertices and an adjacency function. -/
def ofAdj {V : Type} (vs : List V) (adj : V → V → Bool) : Context V :=
  { vertices := vs, isAdj := adj, isMate := emptyMate V }

/-- Add a matching to a context. -/
def withMatching {V : Type} (ctx : Context V) (mate : V → V → Bool) : Context V :=
  { ctx with isMate := mate }

end Context

/-! ## Helpers for `Val` deconstruction -/

namespace Val

@[inline] def asNat {V : Type} : Val V → Option Nat
  | .nat n => some n
  | _ => none

@[inline] def asBool {V : Type} : Val V → Option Bool
  | .bool b => some b
  | _ => none

@[inline] def asVert {V : Type} : Val V → Option V
  | .vert v => some v
  | _ => none

@[inline] def asList {V : Type} : Val V → Option (List (Val V))
  | .list xs => some xs
  | _ => none

@[inline] def asPair {V : Type} : Val V → Option (Val V × Val V)
  | .pair a b => some (a, b)
  | _ => none

@[inline] def asOpt {V : Type} : Val V → Option (Option (Val V))
  | .opt o => some o
  | _ => none

@[inline] def asGraph {V : Type} : Val V → Option (List V × List (V × V))
  | .graph vs es => some (vs, es)
  | _ => none

end Val

/-- Look up a value in an "association list" representation of a map. -/
def Val.assocLookup {V : Type} [DecidableEq V] (key : Val V) :
    List (Val V) → Option (Val V)
  | [] => none
  | (.pair k v) :: rest =>
      if Val.beq k key then some v else assocLookup key rest
  | _ :: rest => assocLookup key rest

/-! ## Built-in dispatch -/

namespace Builtin

variable {V : Type} [DecidableEq V]

/-- Single-arg helper. -/
@[inline] private def unary (args : List (Val V))
    (f : Val V → Option (Val V)) : Option (Val V) :=
  match args with
  | [a] => f a
  | _ => none

/-- Two-arg helper. -/
@[inline] private def binary (args : List (Val V))
    (f : Val V → Val V → Option (Val V)) : Option (Val V) :=
  match args with
  | [a, b] => f a b
  | _ => none

/-- The dispatch table. Returns `none` if `name` is unknown or args ill-typed. -/
def eval (ctx : Context V) (name : String) (args : List (Val V)) :
    Option (Val V) :=
  match name with
  -- ─── Nat ────────────────────────────────────────────────
  | "nat_succ" => unary args fun v => do
      let n ← v.asNat; pure (.nat (n + 1))
  | "nat_pred" => unary args fun v => do
      let n ← v.asNat; pure (.nat (n - 1))
  | "nat_add" => binary args fun a b => do
      let m ← a.asNat; let n ← b.asNat; pure (.nat (m + n))
  | "nat_sub" => binary args fun a b => do
      let m ← a.asNat; let n ← b.asNat; pure (.nat (m - n))
  | "nat_mul" => binary args fun a b => do
      let m ← a.asNat; let n ← b.asNat; pure (.nat (m * n))
  | "nat_eq" => binary args fun a b => do
      let m ← a.asNat; let n ← b.asNat; pure (.bool (m == n))
  | "nat_lt" => binary args fun a b => do
      let m ← a.asNat; let n ← b.asNat; pure (.bool (m < n))
  | "nat_le" => binary args fun a b => do
      let m ← a.asNat; let n ← b.asNat; pure (.bool (m ≤ n))

  -- ─── Bool ───────────────────────────────────────────────
  | "bool_and" => binary args fun a b => do
      let x ← a.asBool; let y ← b.asBool; pure (.bool (x && y))
  | "bool_or" => binary args fun a b => do
      let x ← a.asBool; let y ← b.asBool; pure (.bool (x || y))
  | "bool_not" => unary args fun v => do
      let x ← v.asBool; pure (.bool (!x))

  -- ─── Vertex ─────────────────────────────────────────────
  | "vert_eq" => binary args fun a b => do
      let u ← a.asVert; let v ← b.asVert; pure (.bool (decide (u = v)))

  -- ─── List ──────────────────────────────────────────────
  | "list_cons" => binary args fun h t => do
      let xs ← t.asList; pure (.list (h :: xs))
  | "list_isEmpty" => unary args fun v => do
      let xs ← v.asList; pure (.bool xs.isEmpty)
  | "list_head" => unary args fun v => do
      let xs ← v.asList
      pure (.opt (xs.head?))
  | "list_tail" => unary args fun v => do
      let xs ← v.asList
      pure (.list (xs.tail))
  | "list_length" => unary args fun v => do
      let xs ← v.asList; pure (.nat xs.length)
  | "list_append" => binary args fun a b => do
      let xs ← a.asList; let ys ← b.asList
      pure (.list (xs ++ ys))
  | "list_reverse" => unary args fun v => do
      let xs ← v.asList; pure (.list xs.reverse)
  | "list_contains" => binary args fun x l => do
      let xs ← l.asList
      pure (.bool (xs.any (fun y => Val.beq x y)))

  -- ─── Pair ──────────────────────────────────────────────
  | "pair_mk" => binary args fun a b => some (.pair a b)
  | "pair_fst" => unary args fun v => do
      let (a, _) ← v.asPair; pure a
  | "pair_snd" => unary args fun v => do
      let (_, b) ← v.asPair; pure b

  -- ─── Option ────────────────────────────────────────────
  | "opt_some" => unary args fun v => some (.opt (some v))
  | "opt_isSome" => unary args fun v => do
      let o ← v.asOpt; pure (.bool o.isSome)
  | "opt_isNone" => unary args fun v => do
      let o ← v.asOpt; pure (.bool o.isNone)
  | "opt_getD" => binary args fun o d => do
      let o' ← o.asOpt; pure (o'.getD d)

  -- ─── Association-list "map" ─────────────────────────────
  | "map_lookup" => binary args fun k l => do
      let xs ← l.asList
      pure (.opt (Val.assocLookup k xs))
  | "map_insert" => match args with
    | [k, v, l] => do
        let xs ← l.asList
        let xs' := xs.filter (fun p => match p with
          | .pair k' _ => !Val.beq k k'
          | _ => true)
        pure (.list ((.pair k v) :: xs'))
    | _ => none

  -- ─── Graph ─────────────────────────────────────────────
  | "graph_vertices" => match args with
    | [] => some (.list (ctx.vertices.map .vert))
    | _ => none
  | "graph_hasEdge" => binary args fun a b => do
      let u ← a.asVert; let v ← b.asVert
      pure (.bool (ctx.isAdj u v))
  | "graph_neighbors" => unary args fun v => do
      let u ← v.asVert
      pure (.list ((ctx.vertices.filter (fun w => ctx.isAdj u w)).map .vert))
  | "graph_degree" => unary args fun v => do
      let u ← v.asVert
      pure (.nat (ctx.vertices.filter (fun w => ctx.isAdj u w)).length)

  -- ─── First-class graph values ──────────────────────────
  -- These work on `Val.graph` values rather than the ambient `ctx`.
  -- This is what enables the IR to *pass graphs as arguments* — and
  -- in particular to express the recursion of Edmonds' blossom
  -- algorithm on a *contracted* graph value.

  -- `graph_value_ofCtx` — promote the ambient graph in `ctx` to a
  -- first-class value. Vertex set = `ctx.vertices`, edge list =
  -- pairs `(u, v)` with `u ≠ v` and `ctx.isAdj u v`. This is the
  -- bridge from "ambient ctx" world to "graph as data" world.
  | "graph_value_ofCtx" => match args with
    | [] =>
        let vs := ctx.vertices
        -- Edges: every adjacent pair, oriented `(u, v)` with
        -- index-of-u < index-of-v in `vs` to avoid duplicates.
        let pairs : List (V × V) :=
          (vs.zipIdx).flatMap (fun (u, iu) =>
            (vs.zipIdx).filterMap (fun (v, iv) =>
              if iu < iv ∧ ctx.isAdj u v then some (u, v) else none))
        some (.graph vs pairs)
    | _ => none

  -- `graph_value_vertices g` → `List V` of g's vertices.
  | "graph_value_vertices" => unary args fun gV => do
      let (vs, _) ← gV.asGraph
      pure (.list (vs.map .vert))

  -- `graph_value_edges g` → list of `pair u v`.
  | "graph_value_edges" => unary args fun gV => do
      let (_, es) ← gV.asGraph
      pure (.list (es.map (fun (u, v) => .pair (.vert u) (.vert v))))

  -- `graph_value_hasEdge g u v` → bool.
  | "graph_value_hasEdge" => match args with
    | [gV, uV, vV] => do
        let (_, es) ← gV.asGraph
        let u ← uV.asVert
        let v ← vV.asVert
        pure (.bool
          (es.any (fun e =>
            (decide (e.1 = u) ∧ decide (e.2 = v)) ∨
            (decide (e.1 = v) ∧ decide (e.2 = u)))))
    | _ => none

  -- `graph_value_neighbors g v` → list of vertices adjacent to v in g.
  | "graph_value_neighbors" => binary args fun gV vV => do
      let (_, es) ← gV.asGraph
      let v ← vV.asVert
      let ns : List V :=
        (es.filterMap (fun e =>
          if e.1 = v then some e.2
          else if e.2 = v then some e.1
          else none)).eraseDups
      pure (.list (ns.map .vert))

  -- `graph_value_size g` → number of vertices in g (a `Nat`). This is
  -- the natural well-founded measure for blossom recursion.
  | "graph_value_size" => unary args fun gV => do
      let (vs, _) ← gV.asGraph
      pure (.nat vs.length)

  -- `graph_value_contract g B` — contract the blossom `B` (a list of
  -- vertices, with the head as the *stem*) into the stem.
  --   * The new vertex set is `g.vertices \ (B \ {stem})`.
  --   * Each edge `(u, v)` in `g` is rewritten by sending every
  --     blossom-vertex to the stem; edges that become self-loops are
  --     dropped.
  -- This is the *real* graph-side of `contract_graph` from the
  -- corrected Blossom pseudocode. -/
  | "graph_value_contract" => binary args fun gV bV => do
      let (vs, es) ← gV.asGraph
      let bVs ← bV.asList
      let bverts : List V ← bVs.foldrM
        (fun bvi acc => do let v ← bvi.asVert; pure (v :: acc)) []
      match bverts with
      | [] => some (.graph vs es)             -- empty blossom: no-op
      | stem :: _ =>
          let inB : V → Bool := fun v => bverts.contains v
          let redirect : V → V := fun v => if inB v then stem else v
          -- New vertex list: drop blossom vertices, then add stem at front.
          let nonBlossom : List V := vs.filter (fun v => ¬ inB v)
          let newVs : List V := stem :: nonBlossom
          -- New edges: redirect endpoints, drop self-loops, dedup.
          let rewritten : List (V × V) :=
            (es.filterMap (fun e =>
              let u' := redirect e.1
              let v' := redirect e.2
              if u' = v' then none else some (u', v'))).eraseDups
          some (.graph newVs rewritten)

  -- ─── Matching ──────────────────────────────────────────
  | "matching_isMatched" => unary args fun v => do
      let u ← v.asVert
      pure (.bool (ctx.vertices.any (fun w => ctx.isMate u w)))
  | "matching_isExposed" => unary args fun v => do
      let u ← v.asVert
      pure (.bool (!(ctx.vertices.any (fun w => ctx.isMate u w))))
  | "matching_mate" => unary args fun v => do
      let u ← v.asVert
      pure (.opt ((ctx.vertices.find? (fun w => ctx.isMate u w)).map .vert))
  | "matching_isMatchEdge" => binary args fun a b => do
      let u ← a.asVert; let v ← b.asVert
      pure (.bool (ctx.isMate u v))

  | _ => none      -- unknown built-in name

/-- The set of recognised built-in names (for diagnostics). -/
def isBuiltin (name : String) : Bool :=
  name ∈ [
    "nat_succ", "nat_pred", "nat_add", "nat_sub", "nat_mul",
    "nat_eq", "nat_lt", "nat_le",
    "bool_and", "bool_or", "bool_not",
    "vert_eq",
    "list_cons", "list_isEmpty", "list_head", "list_tail",
    "list_length", "list_append", "list_reverse", "list_contains",
    "pair_mk", "pair_fst", "pair_snd",
    "opt_some", "opt_isSome", "opt_isNone", "opt_getD",
    "map_lookup", "map_insert",
    "graph_vertices", "graph_hasEdge", "graph_neighbors", "graph_degree",
    "graph_value_ofCtx", "graph_value_vertices", "graph_value_edges",
    "graph_value_hasEdge", "graph_value_neighbors",
    "graph_value_size", "graph_value_contract",
    "matching_isMatched", "matching_isExposed", "matching_mate",
    "matching_isMatchEdge"
  ]

end Builtin

end Hackathon.GraphIR
