import Hackathon.GraphIR.Interpreter

/-!
# GraphIR — example programs

A grab-bag of small algorithms to play with. Each is a `Program`
(or a `def` we splice into one) plus a `#eval` showing it run on a
concrete graph. Open this file in the editor to see results.

## Helpers

To keep example bodies readable we abbreviate common AST forms.
-/

namespace Hackathon.GraphIR.Examples

open Expr

/-! ### Tiny syntactic helpers -/

/-- `let x := e in body` (string-named binding). -/
def lt (x : String) (e body : Expr) : Expr := .letE x e body

/-- Variable. -/
def v (x : String) : Expr := .var x

/-- Numeric literal. -/
def nat' (n : Nat) : Expr := .natLit n

/-- Vertex literal (numeric, for `Fin n`-typed graphs). -/
def vert' (i : Nat) : Expr := .vertLit i

/-- Boolean literal. -/
def bool' (b : Bool) : Expr := .boolLit b

/-- Function call. -/
def c (name : String) (args : List Expr) : Expr := .call name args

/-! ### A test graph: K3 (triangle) on `Fin 3` -/

/-- Adjacency for `K3`: `u ≠ v`. -/
private def k3Adj (u v : Fin 3) : Bool := decide (u ≠ v)

/-- The runtime `Context` for `K3`. -/
def k3Ctx : Context (Fin 3) :=
  Context.ofAdj [0, 1, 2] k3Adj

/-- `Config` for `Fin 3` graphs. -/
def cfg3 (ctx : Context (Fin 3)) : Config (Fin 3) :=
  { ctx, vertOfNat := Config.finVertOfNat 3 }

/-! ### A test graph: P4 (path 0—1—2—3) on `Fin 4` -/

private def p4Adj (u v : Fin 4) : Bool :=
  decide (u.val + 1 = v.val ∨ v.val + 1 = u.val)

def p4Ctx : Context (Fin 4) := Context.ofAdj [0, 1, 2, 3] p4Adj

def cfg4 (ctx : Context (Fin 4)) : Config (Fin 4) :=
  { ctx, vertOfNat := Config.finVertOfNat 4 }

/-! ## Examples -/

/-! ### #1 — `id`: the identity function -/

def idProgram : Program where
  funs := [{ name := "id", params := ["x"], body := v "x" }]
  main := c "id" [nat' 42]

#eval Interp.run (cfg3 k3Ctx) 100 idProgram
-- ⇒ some 42

/-! ### #2 — sum of `[1, 2, 3]` via folding by recursion -/

def sumListProgram : Program where
  funs :=
    [ { name := "sum"
        params := ["xs"]
        body :=
          .matchList (v "xs")
            (nat' 0)             -- nil  → 0
            "h" "t"
            (c "nat_add" [v "h", c "sum" [v "t"]])  -- h :: t → h + sum t
      }
    ]
  main :=
    let lit := c "list_cons" [nat' 1,
              c "list_cons" [nat' 2,
              c "list_cons" [nat' 3, .nilE]]]
    c "sum" [lit]

#eval Interp.run (cfg3 k3Ctx) 100 sumListProgram
-- ⇒ some 6

/-! ### #3 — `vertices` / `length` -/

def numVerticesK3 : Program where
  funs := []
  main := c "list_length" [c "graph_vertices" []]

#eval Interp.run (cfg3 k3Ctx) 100 numVerticesK3
-- ⇒ some 3

def numVerticesP4 : Program where
  funs := []
  main := c "list_length" [c "graph_vertices" []]

#eval Interp.run (cfg4 p4Ctx) 100 numVerticesP4
-- ⇒ some 4

/-! ### #4 — neighbours of vertex 1 in K3 -/

def neighbours1K3 : Program where
  funs := []
  main := c "graph_neighbors" [vert' 1]

#eval Interp.run (cfg3 k3Ctx) 100 neighbours1K3
-- ⇒ list of v0 and v2

/-! ### #5 — has edge between vertex 0 and 2 in P4? -/

def edge02P4 : Program where
  funs := []
  main := c "graph_hasEdge" [vert' 0, vert' 2]

#eval Interp.run (cfg4 p4Ctx) 100 edge02P4
-- ⇒ some false

def edge01P4 : Program where
  funs := []
  main := c "graph_hasEdge" [vert' 0, vert' 1]

#eval Interp.run (cfg4 p4Ctx) 100 edge01P4
-- ⇒ some true

/-! ### #6 — degree of vertex 1 in K3 (=2) -/

def degree1K3 : Program where
  funs := []
  main := c "graph_degree" [vert' 1]

#eval Interp.run (cfg3 k3Ctx) 100 degree1K3
-- ⇒ some 2

/-! ### #7 — sum of degrees of all vertices in K3
(`= 2 * |E|` by the handshake lemma; `|E| = 3` for K3, so 6.) -/

def sumOfDegreesK3 : Program where
  funs :=
    [ { name := "sumDeg"
        params := ["xs"]
        body :=
          .matchList (v "xs")
            (nat' 0)
            "h" "t"
            (c "nat_add" [c "graph_degree" [v "h"], c "sumDeg" [v "t"]])
      }
    ]
  main := c "sumDeg" [c "graph_vertices" []]

#eval Interp.run (cfg3 k3Ctx) 100 sumOfDegreesK3
-- ⇒ some 6

/-! ### #8 — count vertices satisfying a predicate
(here: degree exactly 2) -/

def countDeg2K3 : Program where
  funs :=
    [ { name := "count"
        params := ["xs"]
        body :=
          .matchList (v "xs")
            (nat' 0)
            "h" "t"
            (.ite
              (c "nat_eq" [c "graph_degree" [v "h"], nat' 2])
              (c "nat_succ" [c "count" [v "t"]])
              (c "count" [v "t"]))
      }
    ]
  main := c "count" [c "graph_vertices" []]

#eval Interp.run (cfg3 k3Ctx) 100 countDeg2K3
-- ⇒ some 3

/-! ### #9 — list of unmatched vertices

Build a `K3` context with matching `{(0, 1)}`. Vertex `2` should be the
only unmatched vertex.
-/

private def mate01 (u v : Fin 3) : Bool :=
  (decide (u = 0) && decide (v = 1)) || (decide (u = 1) && decide (v = 0))

def k3MatchedCtx : Context (Fin 3) := (k3Ctx.withMatching mate01)

def unmatchedVertices : Program where
  funs :=
    [ { name := "filter"
        params := ["xs"]
        body :=
          .matchList (v "xs")
            .nilE
            "h" "t"
            (.ite
              (c "matching_isExposed" [v "h"])
              (c "list_cons" [v "h", c "filter" [v "t"]])
              (c "filter" [v "t"]))
      }
    ]
  main := c "filter" [c "graph_vertices" []]

#eval Interp.run (cfg3 k3MatchedCtx) 100 unmatchedVertices
-- ⇒ list with v2 only

/-! ### #10 — find the mate of vertex 1 -/

def mateOf1 : Program where
  funs := []
  main := c "matching_mate" [vert' 1]

#eval Interp.run (cfg3 k3MatchedCtx) 100 mateOf1
-- ⇒ some (some v0)

/-! ### #11 — pairs of (vertex, mate) for every matched vertex
Duplicates each edge from both directions. -/

def matchingPairs : Program where
  funs :=
    [ { name := "go"
        params := ["xs"]
        body :=
          .matchList (v "xs") .nilE "h" "t"
            (.matchOpt (c "matching_mate" [v "h"])
              (c "go" [v "t"])
              "m"
              (c "list_cons" [c "pair_mk" [v "h", v "m"], c "go" [v "t"]]))
      }
    ]
  main := c "go" [c "graph_vertices" []]

#eval Interp.run (cfg3 k3MatchedCtx) 100 matchingPairs
-- ⇒ list with two pairs (v0,v1) and (v1,v0)

/-! ### #12 — a tiny "exists an edge from u to v?" check via folding -/

def hasNeighbour : Program where
  funs := []
  main :=
    let neigh := c "graph_neighbors" [vert' 0]
    c "list_contains" [vert' 2, neigh]

#eval Interp.run (cfg3 k3Ctx) 100 hasNeighbour
-- ⇒ some true

end Hackathon.GraphIR.Examples
