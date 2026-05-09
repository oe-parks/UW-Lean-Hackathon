import Hackathon.Graph.Toy.Examples
import Hackathon.Graph.Toy.Walk

/-!
# Concrete graphs used by the exercises

We re-export the few canonical graphs from `Toy.Examples` (`K3`, `K4`,
`P3`, `C4`, `C5`) and add a handful more to give the exercises enough
variety: `P4`, `P5`, `C3`, `K33` (complete bipartite), the bow-tie, and
the star `K1,3`.

All graphs here live on a `Fin n` vertex type so that adjacency is
decidable and the user can lean on `decide` / `fin_cases` to discharge
goals about specific vertices.
-/

namespace Hackathon.Toy.Graph

/-- Path on 4 vertices: `0 — 1 — 2 — 3`. -/
abbrev P4 : Graph (Fin 4) := pathGraph 4

/-- Path on 5 vertices: `0 — 1 — 2 — 3 — 4`. -/
abbrev P5 : Graph (Fin 5) := pathGraph 5

/-- Cycle on 3 vertices (the triangle). Same edges as `K3`. -/
abbrev C3 : Graph (Fin 3) := cycleGraph 3

/--
Complete bipartite graph `K_{3,3}`: vertices `Fin 6`, with sides
`{0,1,2}` and `{3,4,5}`. Adjacency: `u ~ v` iff `u` and `v` are on
opposite sides.
-/
def K33 : Graph (Fin 6) where
  edge u v := (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)
  edge_symm := by
    intro u v h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  edge_irrefl := by intro v h; rcases h with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/--
The *star* `K_{1,3}`: one center (vertex 0) joined to three leaves
(1, 2, 3). No other edges.
-/
def Star4 : Graph (Fin 4) where
  edge u v := (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)
  edge_symm := by
    intro u v h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  edge_irrefl := by intro v h; rcases h with ⟨_, _⟩ | ⟨_, _⟩ <;> contradiction

/--
The *bow-tie*: two triangles `{0,1,2}` and `{2,3,4}` sharing vertex `2`.
Six edges: `0-1, 1-2, 2-0, 2-3, 3-4, 4-2`.
-/
def Bowtie : Graph (Fin 5) where
  edge u v :=
    -- triangle on {0,1,2}: any two distinct from {0,1,2}.
    (u.val ≤ 2 ∧ v.val ≤ 2 ∧ u.val ≠ v.val) ∨
    -- vertex 2 connected to 3 and 4.
    (u.val = 2 ∧ (v.val = 3 ∨ v.val = 4)) ∨
    (v.val = 2 ∧ (u.val = 3 ∨ u.val = 4)) ∨
    -- edge 3-4.
    (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 3)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨h₂, h₁, fun e => h₃ e.symm⟩
    · right; right; left; exact ⟨h₁, h₂⟩
    · right; left; exact ⟨h₁, h₂⟩
    · right; right; right; right; exact ⟨h₂, h₁⟩
    · right; right; right; left; exact ⟨h₂, h₁⟩
  edge_irrefl := by
    intro v h
    rcases h with ⟨_, _, h⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

end Hackathon.Toy.Graph
