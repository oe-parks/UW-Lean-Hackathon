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

open Classical in
/-- Augment the matching by one alternating path. Specified as: if an
augmenting path exists, return `xorWith M w` for some such `w`;
otherwise return `M` unchanged. The actual BFS-based discovery is
abstracted via `Classical.choice` here — the *existence* of the
augmenting path (when one exists) is what's needed for correctness;
the *implementation* lives in the IR (`Hackathon/GraphIR/...`). -/
noncomputable def augmentOnce (_B : Bipartition G) (M : G.Subgraph) : G.Subgraph :=
  if h : ∃ (u : V) (v : V) (w : G.Walk u v), IsAugmenting M w then
    xorWith M h.choose_spec.choose_spec.choose
  else
    M

/-- **Soundness.** `augmentOnce` returns a matching. -/
theorem augmentOnce_isMatching
    (B : Bipartition G) {M : G.Subgraph} (hM : M.IsMatching) :
    (augmentOnce B M).IsMatching := by
  unfold augmentOnce
  by_cases h : ∃ (u : V) (v : V) (w : G.Walk u v), IsAugmenting M w
  · rw [dif_pos h]
    exact h.choose_spec.choose_spec.choose_spec.xorWith_isMatching hM
  · rw [dif_neg h]
    exact hM

/-- **Progress.** If `M` is not maximum, `augmentOnce` strictly increases size. -/
theorem augmentOnce_card_succ
    (B : Bipartition G) {M : G.Subgraph} (hM : M.IsMatching)
    (hNotMax : ¬ IsMaximumMatching M) :
    M.edgeSet.ncard < (augmentOnce B M).edgeSet.ncard := by
  -- M not maximum ⇒ by Berge, an augmenting path exists.
  have hAugExists : ∃ (u : V) (v : V) (w : G.Walk u v), IsAugmenting M w := by
    by_contra hNo
    push_neg at hNo
    apply hNotMax
    exact (berge hM).mpr (fun w => hNo _ _ w)
  unfold augmentOnce
  rw [dif_pos hAugExists]
  -- Result is `xorWith M w` for some aug path w; size = |M| + 1.
  have hcard : (xorWith M hAugExists.choose_spec.choose_spec.choose).edgeSet.ncard
             = M.edgeSet.ncard + 1 :=
    hAugExists.choose_spec.choose_spec.choose_spec.xorWith_card hM
  omega

/-- **Completeness.** If no augmenting path exists, the algorithm returns `M` itself
    (so iterating produces a maximum matching). -/
theorem augmentOnce_eq_self_of_no_augmenting
    (B : Bipartition G) {M : G.Subgraph} (_hM : M.IsMatching)
    (h : ∀ {u v : V} (w : G.Walk u v), ¬ IsAugmenting M w) :
    augmentOnce B M = M := by
  unfold augmentOnce
  rw [dif_neg]
  rintro ⟨u, v, w, hAug⟩
  exact h w hAug

end Hackathon.Bipartite
