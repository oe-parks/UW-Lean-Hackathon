import Mathlib.Data.Set.Defs
import Mathlib.Data.Nat.Notation

/-
# Toy graph framework — warm-up

A from-scratch definition of (simple, undirected) graphs.

After working through this and `Lemmas.lean`, we move to Mathlib's
`SimpleGraph` (see `Bridge.lean`) which has the heavy machinery
(walks, paths, subgraphs, matchings) we will need for Berge's theorem
and the matching-algorithm proofs.

The toy `Graph` is intentionally close to Mathlib's `SimpleGraph` so
that the bridge is essentially a renaming. The point of going through
the warm-up is to get used to defining the basic operations and proving
the elementary lemmas yourself.
-/

namespace Hackathon.Toy

universe u

/--
A *toy graph* on a vertex type `V`: a binary symmetric, irreflexive
relation `edge : V → V → Prop`. We read `G.edge u v` as "there is an
edge between `u` and `v`".
-/
structure Graph (V : Type u) where
  /-- The edge relation. `edge u v` means `u` and `v` are adjacent. -/
  edge : V → V → Prop
  /-- Edges are undirected: `edge u v → edge v u`. -/
  edge_symm : ∀ {u v : V}, edge u v → edge v u
  /-- No self-loops. -/
  edge_irrefl : ∀ v : V, ¬ edge v v

namespace Graph



variable {V : Type u} (G : Graph V)

/-- Convenience alias for the edge relation. Reads as "u is adjacent to v". -/
abbrev Adj (u v : V) : Prop := G.edge u v

/--
The *neighbor set* of a vertex `v`: all vertices adjacent to `v`.
-/
def neighbors (v : V) : Set V := { u | G.edge u v }

/--
A vertex is *isolated* if it has no neighbors.
-/
def IsIsolated (v : V) : Prop := ∀ u, ¬ G.edge u v

/--
Edge set viewed as ordered pairs. Note the same undirected edge `{u,v}`
appears twice here, once as `(u,v)` and once as `(v,u)`. The `Bridge`
file relates this to Mathlib's quotient view via `Sym2`.
-/
def edgePairs : Set (V × V) := { p | G.edge p.1 p.2 }

/--
The *empty graph* on `V`: no edges.
-/
def empty (V : Type u) : Graph V where
  edge _ _ := False
  edge_symm h := h
  edge_irrefl _ h := h

/--
The *complete graph* on `V`: every two distinct vertices are adjacent.
-/
def complete (V : Type u) : Graph V where
  edge u v := u ≠ v
  edge_symm h := fun heq => h heq.symm
  edge_irrefl _ h := h rfl

end Graph

end Hackathon.Toy
