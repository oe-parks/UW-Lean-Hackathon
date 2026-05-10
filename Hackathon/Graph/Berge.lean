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

/- ## Sub-lemmas (Berge proof internals) -/

/-- Lemma A: every vertex has degree at most 2 in `M △ M'`. -/
theorem symmDiff_degree_le_two
    {M M' : G.Subgraph} (hM : M.IsMatching) (hM' : M'.IsMatching) (v : V) :
    True := by trivial  -- placeholder; replace `True` with the real statement

/-- Lemma D: if `|M'| > |M|`, some component of `M △ M'` is an `M`-augmenting path. -/
theorem exists_augmenting_of_larger
    {M M' : G.Subgraph} (hM : M.IsMatching) (hM' : M'.IsMatching)
    (h : M.edgeSet.ncard < M'.edgeSet.ncard) :
    ∃ (u v : V) (w : G.Walk u v), IsAugmenting M w := by
  sorry

/--
**Berge's theorem.** A matching is maximum iff it admits no augmenting path.

The proof reduces to two named obligations:
* `IsAugmenting.xorWith_isMatching` + `IsAugmenting.xorWith_card`
  (the augmentation lemma — produces a strictly larger matching from
  an augmenting path), giving the forward direction.
* `exists_augmenting_of_larger` (the symmetric-difference argument —
  a strictly larger matching gives rise to an augmenting path),
  giving the backward direction.
-/
theorem berge {M : G.Subgraph} (hM : M.IsMatching) (hMFin : M.edgeSet.Finite) :
    IsMaximumMatching M ↔
    ∀ {u v : V} (w : G.Walk u v), ¬ IsAugmenting M w := by
  constructor
  · -- (⇒) M maximum implies no augmenting path.
    rintro ⟨_, hMax⟩ u v w hAug
    -- The augmentation lemma gives a matching of size |M| + 1.
    have h1 : (xorWith M w).IsMatching := hAug.xorWith_isMatching hM
    have h2 : (xorWith M w).edgeSet.ncard = M.edgeSet.ncard + 1 :=
      hAug.xorWith_card hM hMFin
    -- But maximality says |xorWith M w| ≤ |M|. Contradiction.
    have h3 : (xorWith M w).edgeSet.ncard ≤ M.edgeSet.ncard := hMax _ h1
    omega
  · -- (⇐) No augmenting path implies M is maximum.
    intro hNoAug
    refine ⟨hM, ?_⟩
    intro M' hM'
    -- By contradiction: if |M'| > |M|, the symmetric-difference argument
    -- produces an augmenting path, contradicting `hNoAug`.
    by_contra h
    push_neg at h
    obtain ⟨_, _, w, hAug⟩ := exists_augmenting_of_larger hM hM' h
    exact hNoAug w hAug

end Hackathon
