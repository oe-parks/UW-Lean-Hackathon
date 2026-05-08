import Hackathon.Graph.Berge
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-
# Rung 3A — Bipartite matching via alternating BFS

(The Hungarian algorithm / Hopcroft–Karp.)

## Setting

Let `G` be a bipartite graph with parts `L, R : Set V`. Given a
matching `M`, we search for an `M`-augmenting path by BFS:

1. Start the BFS frontier at unmatched left vertices.
2. From the current frontier on the left, follow non-`M` edges to the right.
3. From those right vertices, follow `M` edges back to the left.
4. Repeat until either we hit an unmatched right vertex (= success,
   we found an augmenting path) or the frontier is empty (= failure,
   no augmenting path exists).

## Correctness

**Soundness.** If the BFS reaches an unmatched right vertex, the
backtrace is an `M`-alternating path with both endpoints unmatched
(left endpoint is in the initial frontier, right endpoint by
construction). So it is `M`-augmenting.

**Completeness.** If an `M`-augmenting path exists, the BFS will find
one. Argument: by induction on the length, any augmenting path has its
i-th vertex reachable in BFS layer i.

Combined with Berge's theorem (`Hackathon.berge`), the iterated
"augment until stuck" procedure terminates with a maximum matching.
-/

namespace Hackathon.Bipartite

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A bipartition of `G`: a 2-coloring such that all edges are bichromatic. -/
structure Bipartition (G : SimpleGraph V) where
  side : V → Bool
  edge_bichromatic : ∀ {u v}, G.Adj u v → side u ≠ side v

/-- Augment the matching by one alternating path (specification only).
The implementation will be filled in Phase 2. -/
def augmentOnce (B : Bipartition G) (M : G.Subgraph) : G.Subgraph := sorry

/-- **Soundness.** `augmentOnce` returns a matching. -/
theorem augmentOnce_isMatching
    (B : Bipartition G) {M : G.Subgraph} (hM : M.IsMatching) :
    (augmentOnce B M).IsMatching := by
  sorry

/-- **Progress.** If `M` is not maximum, `augmentOnce` strictly increases size. -/
theorem augmentOnce_card_succ
    (B : Bipartition G) {M : G.Subgraph} (hM : M.IsMatching)
    (hNotMax : ¬ IsMaximumMatching M) :
    M.edgeSet.ncard < (augmentOnce B M).edgeSet.ncard := by
  sorry

/-- **Completeness.** If no augmenting path exists, the algorithm returns `M` itself
    (so iterating produces a maximum matching). -/
theorem augmentOnce_eq_self_of_no_augmenting
    (B : Bipartition G) {M : G.Subgraph} (hM : M.IsMatching)
    (h : ∀ {u v : V} (w : G.Walk u v), ¬ IsAugmenting M w) :
    augmentOnce B M = M := by
  sorry

end Hackathon.Bipartite
