import Mathlib.Combinatorics.SimpleGraph.Basic
import Hackathon.Graph.Toy.Basic

/-
# Bridge: toy `Graph` ↔ Mathlib `SimpleGraph`

Our toy `Graph` is essentially `SimpleGraph` modulo a renaming of the
edge-relation field. This file exhibits the round-trip: every toy
graph gives a Mathlib `SimpleGraph`, every Mathlib `SimpleGraph` gives
a toy graph, and the two operations are mutually inverse.

After this file we use Mathlib's `SimpleGraph` exclusively, since it
brings walks, paths, subgraphs, matchings, and a large theory.
-/

namespace Hackathon.Toy.Graph

universe u
variable {V : Type u}

/-- Convert a toy `Graph` to a Mathlib `SimpleGraph`. -/
def toSimpleGraph (G : Graph V) : SimpleGraph V where
  Adj := G.edge
  symm _ _ h := G.edge_symm h
  loopless := ⟨G.edge_irrefl⟩

/-- Convert a Mathlib `SimpleGraph` to a toy `Graph`. -/
def ofSimpleGraph (G : SimpleGraph V) : Graph V where
  edge := G.Adj
  edge_symm h := G.symm h
  edge_irrefl v h := G.loopless.irrefl v h

/-- The two conversions are mutually inverse (one direction). -/
@[simp] theorem toSimpleGraph_ofSimpleGraph (G : SimpleGraph V) :
    toSimpleGraph (ofSimpleGraph G) = G := by
  rfl

/-- The two conversions are mutually inverse (other direction). -/
@[simp] theorem ofSimpleGraph_toSimpleGraph (G : Graph V) :
    ofSimpleGraph (toSimpleGraph G) = G := by
  rfl

/-- Adjacency commutes with the bridge. -/
@[simp] theorem toSimpleGraph_adj (G : Graph V) (u v : V) :
    (toSimpleGraph G).Adj u v ↔ G.Adj u v := Iff.rfl

end Hackathon.Toy.Graph
