import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Walk

/-
# Matching, alternating walks, augmenting paths

We use Mathlib's `SimpleGraph.Subgraph.IsMatching` as the definition
of a matching: a subgraph in which every vertex has at most one
incident edge.

On top of this we define:

* `IsAlternating M w` — the walk `w` alternates between edges of `M`
  and edges of `G \ M`.
* `IsAugmenting M w` — `w` is an alternating path whose endpoints are
  both unmatched in `M`. (An "M-augmenting path".)

These are the central definitions for Berge's theorem and for
proving correctness of matching algorithms (Phase 2 of the plan).
-/

namespace Hackathon

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/- ## Matching basics -/

/--
A *matching* in `G`: an edge subgraph `M ≤ G.spanningCoe` (i.e. a
subgraph with `M.verts = univ`) whose edges form a matching.
For convenience we work directly with `M : G.Subgraph` and require
`M.IsMatching` (and possibly that `M.verts = Set.univ` for "spanning").

Mathlib reference: `SimpleGraph.Subgraph.IsMatching`.
-/
abbrev Matching (G : SimpleGraph V) := { M : G.Subgraph // M.IsMatching }

/--
A vertex `v` is *unmatched* (free, exposed) in matching `M` if it is
not in `M.verts`. (For an `IsMatching` subgraph, this is equivalent
to "no edge of `M` is incident to `v`".)
-/
def IsUnmatched (M : G.Subgraph) (v : V) : Prop := v ∉ M.verts

/- ## Alternating walks -/

/--
A walk `w` in `G` is *M-alternating* if consecutive edges alternate
between edges of `M` and edges not in `M`. We state this on the
edge sequence `w.edges`.

Equivalent formulation: for every two consecutive edges `e₁, e₂` in
the walk, exactly one of them lies in `M.edgeSet`.
-/
def IsAlternating (M : G.Subgraph) {u v : V} (w : G.Walk u v) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i + 1 < w.edges.length),
    (w.edges[i]'(Nat.lt_of_succ_lt hi) ∈ M.edgeSet) ≠
    (w.edges[i + 1]'hi ∈ M.edgeSet)

/- ## Augmenting paths -/

/--
A walk `w` from `u` to `v` is `M`-*augmenting* iff:
1. it is a path (no repeated vertices),
2. it is `M`-alternating,
3. its first edge is *not* in `M`,
4. its last edge is *not* in `M` (equivalently, both endpoints are
   unmatched).

The first/last conditions force the walk's edge sequence to be of the
form  `e₀ ∉ M, e₁ ∈ M, e₂ ∉ M, …, eₖ ∉ M`, with `k` even, so the path
has odd length and "augmenting via symmetric difference" gives a
matching one larger than `M`.
-/
structure IsAugmenting (M : G.Subgraph) {u v : V} (w : G.Walk u v) : Prop where
  isPath        : w.IsPath
  alternating   : IsAlternating M w
  startUnmatched : IsUnmatched M u
  endUnmatched   : IsUnmatched M v

/- ## Practice lemmas -/

/-- ★  The empty subgraph is a matching. -/
example : (⊥ : G.Subgraph).IsMatching := by
  -- HINT: unfold `IsMatching`. The hypothesis `M.Adj u v` is impossible.
  sorry

/-- ★★  In a matching, adjacency is a *partial function*: each vertex has at
most one match. -/
example {M : G.Subgraph} (hM : M.IsMatching) {u v w : V}
    (huv : M.Adj u v) (huw : M.Adj u w) : v = w := by
  -- HINT: unfold `IsMatching`. Apply `hM` at `u`, get unique-existence.
  sorry

/-- ★★  The empty walk is alternating in any matching `M` (vacuously). -/
example (M : G.Subgraph) (v : V) :
    IsAlternating M (Walk.nil : G.Walk v v) := by
  -- HINT: unfold `IsAlternating`. The walk has no edges, so the
  --       hypothesis `i + 1 < 0` is impossible.
  sorry

/-- ★★★  In a *bipartite* graph, every augmenting path has odd length.
(Sketch only — finish in Phase 2.) -/
example {M : G.Subgraph} {u v : V} (w : G.Walk u v) (h : IsAugmenting M w) :
    Odd w.length := by
  -- HINT: a path that starts and ends with non-`M` edges and alternates
  --       has an even number of `M` edges and odd total length.
  sorry

end Hackathon
