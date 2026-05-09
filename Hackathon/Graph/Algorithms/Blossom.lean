import Hackathon.Graph.Berge

/-
# Rung 3B — Edmonds' blossom algorithm (general matching)

This is the **stretch goal** — there is no full mechanization of
Edmonds' algorithm in Lean / Mathlib at the time of writing, so partial
progress is itself a research contribution.

## Why bipartite isn't enough

In a non-bipartite graph, the bipartite alternating-BFS argument
breaks: an alternating walk can revisit a vertex via an *odd cycle*
(a "blossom"), and the BFS can't tell whether to mark such a
vertex as a "left" or "right" layer.

## The blossom trick

Edmonds' insight: when BFS finds two same-layer vertices joined by an
edge, they sit on a *blossom* — an odd-length alternating cycle
through some "stem" vertex. Contract the blossom to a single
super-vertex and recurse on the smaller graph. If the recursive call
finds an augmenting path through the super-vertex, *lift* the path
back into the original graph by routing it appropriately around the
blossom (always feasible because the cycle is odd).

## Roadmap of definitions

* `Blossom` — an odd alternating cycle with a designated stem.
* `contract G B` — quotient `G` by collapsing the blossom `B`.
* `lift` — given an augmenting path in the contracted graph,
  produce one in the original.

## Roadmap of theorems

1. **Blossom contraction preserves matching size correspondence:**
   matchings in `contract G B` are in bijection with matchings in `G`
   that "respect" `B`.
2. **Lifting preserves augmenting:** an augmenting path in the
   contracted graph lifts to an augmenting path in `G`.
3. **Edmonds' algorithm correctness:** the recursive contract-and-lift
   procedure finds an `M`-augmenting path iff one exists.
4. Combined with Berge: iterated augmentation terminates with maximum
   matching.

Each of these is a substantial theorem. We leave them as `sorry`s here
and treat partial progress as Phase 3 / future work.
-/

namespace Hackathon.Edmonds

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A *blossom* with respect to matching `M`: an odd-length closed
walk that is `M`-alternating and starts/ends at an `M`-exposed vertex
(the *stem*). -/
structure Blossom (M : G.Subgraph) where
  stem : V
  cycle : G.Walk stem stem
  oddLength : Odd cycle.length
  isAlternating : Hackathon.IsAlternating M cycle

/-- Contract a blossom to a single vertex. Construction TBD. -/
def contract (B : Blossom (G := G) M) : SimpleGraph V := sorry

/-- Lift an augmenting path in `contract B` to one in `G`. -/
theorem lift_augmenting
    {M : G.Subgraph} (B : Blossom (G := G) M)
    {u v : V} (w : (contract B).Walk u v)
    -- (h : the lifted notion of IsAugmenting in contract)
    : ∃ (u' v' : V) (w' : G.Walk u' v'), Hackathon.IsAugmenting M w' := by
  sorry

/-- Edmonds: if `G` has an `M`-augmenting path, the algorithm finds one. -/
theorem edmonds_finds_augmenting
    {M : G.Subgraph} (hM : M.IsMatching)
    (h : ∃ (u v : V) (w : G.Walk u v), Hackathon.IsAugmenting M w) :
    ∃ (u v : V) (w : G.Walk u v), Hackathon.IsAugmenting M w := by
  sorry

end Hackathon.Edmonds
