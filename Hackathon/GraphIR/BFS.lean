import Hackathon.GraphIR.Examples

/-!
# Breadth-first search in GraphIR

`bfsProgram` computes, given a source vertex `s`, an association map
from each reachable vertex `v` to the shortest path length from `s`.

Implementation (functional / SSA, using mutual recursion):

```
bfs_step(queue, dist) =
  match queue with
  | []          => dist                             // done
  | (u, d) :: rest =>
      process_ns(rest, dist, neighbors(u), d)

process_ns(queue, dist, ns, d) =
  match ns with
  | []      => bfs_step(queue, dist)
  | n :: rest =>
      if isSome(map_lookup(n, dist))                // already visited
      then process_ns(queue, dist, rest, d)
      else
        let dist'  = map_insert(n, d+1, dist)
        let queue' = list_append(queue, [(n, d+1)])
        process_ns(queue', dist', rest, d)

bfs(s) =
  bfs_step([(s, 0)], map_insert(s, 0, []))
```

We expose three things:

* `bfsProgram` — the IR program, runnable via `#eval`.
* `runBFS` — convenience wrapper that takes a source vertex literal.
* A correctness scaffold: `theorem bfs_correct` stating the headline
  result, with the proof's deeper parts left as `sorry` for later.
-/

namespace Hackathon.GraphIR.BFS

open Hackathon.GraphIR Examples

/-! ## The BFS program -/

/-- The mutually-recursive `bfs_step` and `process_ns`, plus the
    top-level `bfs(s)` wrapper. -/
def bfsFuns : List FunDecl :=
  [ { name := "bfs_step"
      params := ["queue", "dist"]
      body :=
        .matchList (v "queue")
          (v "dist")                           -- queue empty → return dist
          "head" "rest"
          (.matchPair (v "head") "u" "d"
            (c "process_ns"
              [ v "rest"
              , v "dist"
              , c "graph_neighbors" [v "u"]
              , v "d"
              ]))
    }
  , { name := "process_ns"
      params := ["queue", "dist", "ns", "d"]
      body :=
        .matchList (v "ns")
          (c "bfs_step" [v "queue", v "dist"])    -- no more neighbors
          "n" "rest"
          (.ite
            (c "opt_isSome" [c "map_lookup" [v "n", v "dist"]])
              -- already visited
              (c "process_ns" [v "queue", v "dist", v "rest", v "d"])
              -- new: enqueue and record distance d+1
              (lt "d1" (c "nat_succ" [v "d"])
              (lt "dist1" (c "map_insert" [v "n", v "d1", v "dist"])
              (lt "queue1" (c "list_append"
                              [ v "queue"
                              , c "list_cons"
                                  [c "pair_mk" [v "n", v "d1"], .nilE]
                              ])
              (c "process_ns"
                [v "queue1", v "dist1", v "rest", v "d"])))))
    }
  , { name := "bfs"
      params := ["s"]
      body :=
        lt "init_pair" (c "pair_mk" [v "s", nat' 0])
        (lt "init_queue" (c "list_cons" [v "init_pair", .nilE])
        (lt "init_dist" (c "map_insert" [v "s", nat' 0, .nilE])
        (c "bfs_step" [v "init_queue", v "init_dist"])))
    }
  ]

/-- The BFS program, run from vertex `s`, returns its distance map. -/
def bfsProgram (sIdx : Nat) : Program where
  funs := bfsFuns
  main := c "bfs" [vert' sIdx]

/-! ## Run BFS on the example graphs -/

#eval Interp.run (cfg3 k3Ctx) 1000 (bfsProgram 0)
-- triangle K3 from vertex 0: every other vertex at distance 1
-- ⇒ (some) [(v2, 1), (v1, 1), (v0, 0)]   (order may vary)

#eval Interp.run (cfg4 p4Ctx) 1000 (bfsProgram 0)
-- path 0—1—2—3 from vertex 0: distances 0, 1, 2, 3.
-- ⇒ (some) [(v3, 3), (v2, 2), (v1, 1), (v0, 0)]

#eval Interp.run (cfg4 p4Ctx) 1000 (bfsProgram 2)
-- path from vertex 2: distances 2, 1, 0, 1 for v0, v1, v2, v3.

/-! ## A reference BFS implementation in Lean

To state and prove correctness without unfolding the entire interpreter,
we lift the IR program into a regular Lean function that does the same
thing. Then the correctness theorem has two halves:

1. `bfsLean` is correct (uses graph theory of `Toy.Walk`).
2. `bfsProgram` and `bfsLean` agree (computational equivalence). -/

variable {V : Type} [DecidableEq V]

/-- Pure-Lean BFS reference. Returns an association list from every
    reachable vertex to its shortest-path distance from `s`. -/
def bfsLean (ctx : Context V) (s : V) : List (V × Nat) :=
  let rec go (fuel : Nat) (queue : List (V × Nat)) (dist : List (V × Nat)) :
      List (V × Nat) :=
    match fuel with
    | 0 => dist
    | fuel + 1 =>
      match queue with
      | [] => dist
      | (u, d) :: rest =>
        let ns := ctx.vertices.filter (fun w => ctx.isAdj u w)
        let unvisited := ns.filter (fun n => (dist.lookup n).isNone)
        let newPairs := unvisited.map (fun n => (n, d + 1))
        go fuel (rest ++ newPairs) (newPairs ++ dist)
  -- Bound by `|V|² + 1`, which is a safe upper bound on BFS work.
  let bound := ctx.vertices.length * ctx.vertices.length + 1
  go bound [(s, 0)] [(s, 0)]

/-! ## Correctness scaffold

Two correctness statements, in increasing strength:

1. **Soundness**: if `(v, d) ∈ bfsLean ctx s`, then there is a walk of
   length `d` from `s` to `v`.
2. **Optimality**: that `d` is the *shortest* such length.

We state both and leave the proofs as `sorry` — the headline
deliverable of this file is "BFS in GraphIR runs and produces the right
output on examples"; the full correctness proof is the next milestone.
-/

/-- Reachability via a `Toy.Walk`. -/
def Reachable (G : Toy.Graph V) (s v : V) : Prop :=
  ∃ (w : Toy.Walk G s v), True

/-- "There is a walk of length exactly `d` from `s` to `v`". -/
def WalkOfLength (G : Toy.Graph V) (s v : V) (d : Nat) : Prop :=
  ∃ (w : Toy.Walk G s v), w.length = d

/-- **Soundness.** Every `(v, d)` returned by `bfsLean` corresponds to
    an actual walk of length `d` in `G`. Bridge between context and
    graph: `ctx.isAdj u w = true ↔ G.edge u w`. -/
theorem bfsLean_sound (G : Toy.Graph V) (ctx : Context V)
    (h_adj : ∀ u w, ctx.isAdj u w = true ↔ G.edge u w)
    (s v : V) (d : Nat) :
    (v, d) ∈ bfsLean ctx s → WalkOfLength G s v d := by
  -- Proof by induction on the BFS fuel, using the invariant
  -- "every (u, e) on the queue is reachable in exactly e steps".
  sorry

/-- **Optimality.** The distance `d` returned by `bfsLean` is the
    *shortest* walk length from `s` to `v`: any other walk is at least
    as long. -/
theorem bfsLean_optimal (G : Toy.Graph V) (ctx : Context V)
    (h_adj : ∀ u w, ctx.isAdj u w = true ↔ G.edge u w)
    (s v : V) (d : Nat) :
    (v, d) ∈ bfsLean ctx s →
    ∀ d' (_ : WalkOfLength G s v d'), d ≤ d' := by
  -- Standard BFS-layer argument: a vertex is popped from the queue
  -- before any longer-distance vertex.
  sorry

end Hackathon.GraphIR.BFS
