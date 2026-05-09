import Hackathon.Graph.Toy.Basic

/-!
# Matchings in the toy graph layer

A *matching* in a `Graph G` on vertex type `V` is a sub-relation `edge`
with the same symmetry/irreflexivity as `G`, contained in `G.edge`,
in which every vertex is incident to at most one edge.

This is the from-scratch counterpart of Mathlib's
`SimpleGraph.Subgraph.IsMatching`.  We use it for the practice
exercises in `Hackathon/Exercises/`; for the "real" theorems
(Berge, augmentation lemma) we still go through the Mathlib layer.
-/

namespace Hackathon.Toy

universe u

variable {V : Type u}

/--
A *matching* in a `Graph G` is a symmetric, irreflexive sub-relation of
`G.edge` in which each vertex has at most one partner.

`edge u v` reads "the matching pairs `u` with `v`".
-/
structure Matching (G : Graph V) where
  /-- Pairs in the matching. `edge u v` means "matched as a pair". -/
  edge : V → V → Prop
  /-- Matching edges are undirected. -/
  edge_symm : ∀ {u v : V}, edge u v → edge v u
  /-- No self-pairing. -/
  edge_irrefl : ∀ v : V, ¬ edge v v
  /-- Every matching edge is an edge of the underlying graph. -/
  edge_subgraph : ∀ {u v : V}, edge u v → G.edge u v
  /-- Each vertex has at most one partner. -/
  unique : ∀ {u v w : V}, edge u v → edge u w → v = w

namespace Matching

variable {G : Graph V} (M : Matching G)

/-- A vertex is *matched* in `M` if some edge of `M` is incident to it. -/
def IsMatched (v : V) : Prop := ∃ u, M.edge u v

/-- A vertex is *unmatched* (free, exposed) in `M` if no edge of `M` is incident to it. -/
def IsUnmatched (v : V) : Prop := ∀ u, ¬ M.edge u v

@[simp] theorem isUnmatched_iff_not_isMatched (v : V) :
    M.IsUnmatched v ↔ ¬ M.IsMatched v := by
  simp [IsUnmatched, IsMatched, not_exists]

/-- The *empty matching*: no edges. -/
def empty (G : Graph V) : Matching G where
  edge _ _ := False
  edge_symm h := h
  edge_irrefl _ h := h
  edge_subgraph h := h.elim
  unique h _ := h.elim

@[simp] theorem empty_edge {u v : V} : (empty G).edge u v ↔ False := Iff.rfl

@[simp] theorem empty_isUnmatched (v : V) : (empty G).IsUnmatched v := by
  intro u h; exact h

end Matching

end Hackathon.Toy
