import Hackathon.Graph.Matching

/-
# Rung 1 — The augmentation lemma

If `P` is an `M`-augmenting path, then the *symmetric difference*
`M △ edges(P)` is again a matching, and its size is `|M| + 1`.

This is the engine of every matching algorithm: each augmenting path
strictly increases the matching size by 1, so we can only find at most
|V|/2 of them.

## Sub-lemmas

* `xor_subgraph M w` — the symmetric difference of `M.edgeSet` and
  the edges of `w`, viewed as a subgraph.
* Adjacency in the xor: `(M △ w).Adj a b ↔ (M.Adj a b ↔ s(a,b) ∉ w.edges)`.
* The xor is a matching when `w` is `M`-augmenting: every vertex has
  at most one incident edge.
* The xor has `|M| + 1` edges (one fewer `M`-edge, two more new edges,
  net +1, because the path has even number of `M`-edges interspersed
  with one more non-`M`-edge).

We leave statements with `sorry` for now. Filling these in is **Phase 2,
Rung 1** of the plan.
-/

namespace Hackathon

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/--
The symmetric difference of a matching `M` with the edges of a walk `w`,
returned as a subgraph of `G`. Adjacency:

  `Adj a b` iff exactly one of `M.Adj a b` and `s(a,b) ∈ w.edges` holds
  (and `G.Adj a b`, to remain a subgraph of `G`).
-/
def xorWith (M : G.Subgraph) {u v : V} (w : G.Walk u v) : G.Subgraph where
  verts := Set.univ
  Adj a b := G.Adj a b ∧ (M.Adj a b ↔ s(a, b) ∉ w.edges)
  adj_sub h := h.1
  edge_vert _ := Set.mem_univ _
  symm := by
    intro a b ⟨hab, hxor⟩
    refine ⟨hab.symm, ?_⟩
    rw [show s(b, a) = s(a, b) from Sym2.eq_swap]
    constructor
    · intro h
      exact hxor.mp (M.symm h)
    · intro h
      exact M.symm (hxor.mpr h)

/--
**Augmentation lemma.** If `w` is `M`-augmenting, then `xorWith M w`
is a matching.
-/
theorem IsAugmenting.xorWith_isMatching
    {M : G.Subgraph} (hM : M.IsMatching) {u v : V}
    {w : G.Walk u v} (hw : IsAugmenting M w) :
    (xorWith M w).IsMatching := by
  sorry

/--
**Augmentation lemma — size.** If `w` is `M`-augmenting and the
underlying graph is finite, then `|xorWith M w| = |M| + 1`.
We state this with `Set.ncard` on edge sets.
-/
theorem IsAugmenting.xorWith_card
    {M : G.Subgraph} (hM : M.IsMatching) {u v : V}
    {w : G.Walk u v} (hw : IsAugmenting M w) :
    (xorWith M w).edgeSet.ncard = M.edgeSet.ncard + 1 := by
  sorry

end Hackathon
