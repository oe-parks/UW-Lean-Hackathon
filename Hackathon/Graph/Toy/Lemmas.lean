import Hackathon.Graph.Toy.Basic
import Hackathon.Graph.Toy.Examples

/-
# Practice lemmas — toy graph framework

A graded set of exercises. Each lemma is stated and a proof skeleton
is given with `sorry` (or a partial proof). Replace each `sorry` with
a real proof.

Difficulty markers in comments:
  ★      easy (one line, intro/exact/rfl)
  ★★     moderate (a few tactics, case analysis)
  ★★★   harder (chained reasoning or working through definitions)

Hints follow the lemma in a `--` comment.
-/

namespace Hackathon.Toy.Graph

universe u
variable {V : Type u} (G : Graph V)

/- ## Section 1: Adjacency basics -/

/-- ★  Adjacency is symmetric. (Practice using `G.edge_symm`.) -/
theorem adj_symm {u v : V} (h : G.Adj u v) : G.Adj v u := by
  -- HINT: `G.edge_symm` is exactly this fact, but `Adj` and `edge` are
  -- definitionally equal so `exact` should close it.
  sorry

/-- ★  An edge cannot connect a vertex to itself. -/
theorem not_adj_self (v : V) : ¬ G.Adj v v := by
  -- HINT: Use `G.edge_irrefl`.
  sorry

/-- ★★  If `u` is adjacent to `v`, then `u ≠ v`. -/
theorem adj_ne {u v : V} (h : G.Adj u v) : u ≠ v := by
  -- HINT: assume `u = v`, then derive a self-loop, contradicting `not_adj_self`.
  sorry

/-- ★★  Adjacency is symmetric, as an iff. -/
theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u := by
  -- HINT: split with `constructor` (or `Iff.intro`) and reuse `adj_symm`.
  sorry

/- ## Section 2: The empty and complete graphs -/

/-- ★  The empty graph has no edges. -/
theorem empty_no_edges (u v : V) : ¬ (Graph.empty V).Adj u v := by
  -- HINT: unfold `Graph.empty`. The edge predicate is `False`.
  sorry

/-- ★  In the complete graph, two vertices are adjacent iff they are distinct. -/
theorem complete_adj_iff (u v : V) : (Graph.complete V).Adj u v ↔ u ≠ v := by
  -- HINT: by definition of `Graph.complete`, this is `Iff.rfl`.
  sorry

/-- ★★  Every non-trivial complete graph has at least one edge. -/
theorem complete_has_edge {u v : V} (h : u ≠ v) :
    (Graph.complete V).Adj u v := by
  -- HINT: unfold `complete`; the goal becomes `u ≠ v`.
  sorry

/- ## Section 3: Neighborhoods and isolation -/

/-- ★  An isolated vertex has empty neighbor set. -/
theorem isolated_neighbors_empty {v : V} (h : G.IsIsolated v) :
    G.neighbors v = ∅ := by
  -- HINT: a set is `∅` iff it has no elements; use `Set.eq_empty_iff_forall_notMem`.
  sorry

/-- ★★  In `Graph.empty`, every vertex is isolated. -/
theorem empty_all_isolated (v : V) : (Graph.empty V).IsIsolated v := by
  -- HINT: unfold `IsIsolated` and `Graph.empty`. The hypothesis is `False`.
  sorry

/- ## Section 4: Concrete graphs -/

/-- ★  In `K3`, vertex `0` is adjacent to vertex `1`. -/
theorem K3_adj_0_1 : K3.Adj 0 1 := by
  -- HINT: `K3 = complete (Fin 3)`. Adjacency is `0 ≠ 1`. Use `decide`.
  sorry

/-- ★  In `P3`, vertex `0` is *not* adjacent to vertex `2`. -/
theorem P3_not_adj_0_2 : ¬ P3.Adj 0 2 := by
  -- HINT: unfold `P3 = pathGraph 3`. The edge predicate is two equalities,
  --       both contradictory. `decide` should work.
  sorry

/-- ★★  Path graphs are subgraphs of cycle graphs (for n ≥ 2). -/
theorem path_subset_cycle (n : ℕ) (u v : Fin n) :
    (pathGraph n).Adj u v → (cycleGraph n).Adj u v := by
  -- HINT: unfold both definitions. The path edge predicate is one of the
  --       cycle disjuncts. Show the `u ≠ v` part using `omega` on `u.val + 1 = v.val`.
  sorry

end Hackathon.Toy.Graph
