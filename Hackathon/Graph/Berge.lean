import Hackathon.Graph.Augment

/-
# Rung 2 — Berge's theorem

> A matching `M` in a graph `G` is maximum if and only if `G` has no
> `M`-augmenting path.

This is **the** correctness criterion: any algorithm that "keeps
finding augmenting paths until none exist" terminates with a maximum
matching, by Berge's theorem. So once Berge is proved, the burden of
proving algorithm correctness is reduced to showing search-completeness
(the algorithm finds an augmenting path whenever one exists).

## Proof outline

(⇐) If there is an `M`-augmenting path, the augmentation lemma
(`Hackathon.Augment`) produces a strictly larger matching, so `M` is
not maximum. Contrapositive of the right-to-left direction.

(⇒) The hard direction. Suppose `M` is not maximum: pick a matching
`M'` with `|M'| > |M|`. Look at the *symmetric difference*
`H := M △ M'` viewed as a subgraph.

  Lemma A. In `H`, every vertex has degree ≤ 2 (since `M` and `M'`
  each contribute ≤ 1).

  Lemma B. So every connected component of `H` is a path or a cycle.

  Lemma C. Every cycle has even length and contributes equally to `M`
  and `M'` (alternating edges).

  Lemma D. Therefore some path-component has more `M'`-edges than
  `M`-edges — call it `P`.

  Lemma E. `P`'s endpoints have degree 1 in `H`. Their `H`-edge must
  be an `M'`-edge (else `M` covers them; one can check the count
  works out). So both endpoints are `M`-unmatched, meaning `P` is an
  `M`-augmenting path.

Each lemma is independent and can be tackled separately.
-/

namespace Hackathon

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/--
A matching is *maximum* if no other matching has strictly larger size.
(Defined via `Set.ncard` on the edge set.)
-/
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧
  ∀ M' : G.Subgraph, M'.IsMatching →
    M'.edgeSet.ncard ≤ M.edgeSet.ncard

/--
**Berge's theorem.** A matching is maximum iff it admits no augmenting path.
-/
theorem berge {M : G.Subgraph} (hM : M.IsMatching) :
    IsMaximumMatching M ↔
    ∀ {u v : V} (w : G.Walk u v), ¬ IsAugmenting M w := by
  sorry

/- ## Sub-lemmas (Berge proof internals) -/

/-- Lemma A: every vertex has degree at most 2 in `M △ M'`. -/
theorem symmDiff_degree_le_two
    {M M' : G.Subgraph} (hM : M.IsMatching) (hM' : M'.IsMatching) (v : V) :
    True := by sorry  -- placeholder; replace `True` with the real statement

/-- Lemma D: if `|M'| > |M|`, some component of `M △ M'` is an `M`-augmenting path. -/
theorem exists_augmenting_of_larger
    {M M' : G.Subgraph} (hM : M.IsMatching) (hM' : M'.IsMatching)
    (h : M.edgeSet.ncard < M'.edgeSet.ncard) :
    ∃ (u v : V) (w : G.Walk u v), IsAugmenting M w := by
  sorry

end Hackathon
