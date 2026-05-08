import Hackathon.Graph.Toy.Basic

/-
# Concrete toy graphs

Some named graphs to play with: complete graphs `K n`, path graphs
`pathGraph n`, and cycle graphs `cycleGraph n`. These are useful as
test cases for the practice lemmas.
-/

namespace Hackathon.Toy.Graph

universe u

/-- The complete graph on `Fin n`. -/
def K (n : ℕ) : Graph (Fin n) := complete (Fin n)

/-- `K3` — the triangle. -/
abbrev K3 : Graph (Fin 3) := K 3

/-- `K4` — the complete graph on 4 vertices. -/
abbrev K4 : Graph (Fin 4) := K 4

/--
The *path graph* on `Fin n`: vertices `0, 1, …, n-1` connected in a line.
Adjacency: `u` and `v` are connected iff their values differ by exactly 1.
-/
def pathGraph (n : ℕ) : Graph (Fin n) where
  edge u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  edge_symm h := h.symm
  edge_irrefl v h := by
    rcases h with h | h <;> omega

/-- `P3` — the path 0 — 1 — 2. -/
abbrev P3 : Graph (Fin 3) := pathGraph 3

/--
The *cycle graph* on `Fin n`: vertices `0, 1, …, n-1` connected in a ring.
Adjacency: like `pathGraph`, plus an extra edge between `0` and `n-1`.

The `u ≠ v` guard ensures irreflexivity even when `n = 1` (where the
"wrap-around" disjunct would otherwise create a self-loop).
-/
def cycleGraph (n : ℕ) : Graph (Fin n) where
  edge u v := u ≠ v ∧
    ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val) ∨
     (u.val = 0 ∧ v.val + 1 = n) ∨ (v.val = 0 ∧ u.val + 1 = n))
  edge_symm := by
    rintro u v ⟨hne, hor⟩
    refine ⟨hne.symm, ?_⟩
    rcases hor with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  edge_irrefl v h := h.1 rfl

/-- `C4` — the 4-cycle. -/
abbrev C4 : Graph (Fin 4) := cycleGraph 4

/-- `C5` — the 5-cycle (odd cycle, useful for blossom examples). -/
abbrev C5 : Graph (Fin 5) := cycleGraph 5

end Hackathon.Toy.Graph
