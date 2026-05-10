import Hackathon.Exercises.Worked

/-!
# Exercises: matchings on concrete graphs

Each `example` is a `sorry`-stub for you to fill in. Hints are in
comments above the `sorry`. When in doubt, `Worked.lean` is the
template — the patterns there carry over directly.

Difficulty:  ★ easy   ★★ moderate   ★★★ harder

The exercises are tilted toward the harder end (per the user's
preference) — most stars are ★★ or ★★★.
-/

namespace Hackathon.Toy.Exercises.Matchings

open Hackathon.Toy Graph

/-! ## Adjacency drills -/

/-- ★  In `K3`, vertex `0` and `1` are adjacent. -/
example : K3.edge (0 : Fin 3) 1 := Fin.ne_of_val_ne (by omega)

/-- ★  In `K4`, vertex `0` is *not* adjacent to itself. -/
example : ¬ K4.edge (0 : Fin 4) 0 := K4.edge_irrefl 0

/-- ★★  In `C5`, vertices `0` and `4` are adjacent (the wrap-around edge). -/
example : C5.edge (0 : Fin 5) 4 := by
  refine ⟨by decide, ?_⟩
  right; right; left; exact ⟨rfl, rfl⟩

/-- ★★  In `P5`, vertices `0` and `2` are *not* adjacent. -/
example : ¬ P5.edge (0 : Fin 5) 2 := by
  intro h; rcases h with h | h <;> omega

/-- ★★  In `Star4`, the center `0` is adjacent to leaf `2`. -/
example : Star4.edge (0 : Fin 4) 2 := Or.inl ⟨rfl, by decide⟩

/-- ★★  In `Star4`, leaves `1` and `2` are *not* adjacent. -/
example : ¬ Star4.edge (1 : Fin 4) 2 := by
  intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- ★★  In `Bowtie`, the shared vertex `2` is adjacent to `4`. -/
example : Bowtie.edge (2 : Fin 5) 4 := Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)

/-- ★★★  In `K33`, vertices `1` (left side) and `4` (right side) are adjacent. -/
example : K33.edge (1 : Fin 6) 4 := Or.inl ⟨by decide, by decide⟩

/-- ★★★  In `K33`, two left-side vertices `0` and `1` are *not* adjacent. -/
example : ¬ K33.edge (0 : Fin 6) 1 := by
  intro h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-! ## Building matchings

Recall: a `Matching G` is a structure with five fields. Constructing it
is the proof that the chosen edges form a matching. Pattern from
`Worked.lean §2`.
-/

/-- ★★  The single-edge matching `{(0, 1)}` on `P4`. -/
def M01_P4 : Matching P4 where
  edge u v := (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂, h₁⟩
    · exact Or.inl ⟨h₂, h₁⟩
  edge_irrefl := by
    intro v h; rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  edge_subgraph := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  unique := by
    intro u v w huv huw
    apply Fin.ext
    rcases huv with ⟨_, hv⟩ | ⟨_, hv⟩ <;>
    rcases huw with ⟨_, hw⟩ | ⟨_, hw⟩ <;> omega

/-- ★★  The single-edge matching `{(2, 3)}` on `P4`. -/
def M23_P4 : Matching P4 where
  edge u v := (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂, h₁⟩
    · exact Or.inl ⟨h₂, h₁⟩
  edge_irrefl := by
    intro v h; rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  edge_subgraph := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  unique := by
    intro u v w huv huw
    apply Fin.ext
    rcases huv with ⟨_, hv⟩ | ⟨_, hv⟩ <;>
    rcases huw with ⟨_, hw⟩ | ⟨_, hw⟩ <;> omega

/-- ★★★  A perfect matching on `P4`: `{(0, 1), (2, 3)}`. -/
def MperfP4 : Matching P4 where
  edge u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr (Or.inl ⟨h₂, h₁⟩)
    · exact Or.inl ⟨h₂, h₁⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h₂, h₁⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h₂, h₁⟩))
  edge_irrefl := by
    intro v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  edge_subgraph := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  unique := by
    intro u v w huv huw
    apply Fin.ext
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
    rcases huw with ⟨hu', hw⟩ | ⟨hu', hw⟩ | ⟨hu', hw⟩ | ⟨hu', hw⟩ <;> omega

/-- ★★★  A perfect matching on `K4`: `{(0, 1), (2, 3)}`. -/
def MperfK4 : Matching K4 where
  edge u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr (Or.inl ⟨h₂, h₁⟩)
    · exact Or.inl ⟨h₂, h₁⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h₂, h₁⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h₂, h₁⟩))
  edge_irrefl := by
    intro v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  edge_subgraph := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      exact Fin.ne_of_val_ne (by omega)
  unique := by
    intro u v w huv huw
    apply Fin.ext
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
    rcases huw with ⟨hu', hw⟩ | ⟨hu', hw⟩ | ⟨hu', hw⟩ | ⟨hu', hw⟩ <;> omega

/-- ★★  The single matching edge `(2, 4)` of the bow-tie. -/
def Mbowtie : Matching Bowtie where
  edge u v := (u.val = 2 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 2)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂, h₁⟩
    · exact Or.inl ⟨h₂, h₁⟩
  edge_irrefl := by
    intro v h; rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  edge_subgraph := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · -- u.val = 2, v.val = 4: 2 connected to 4 via second triangle.
      exact Or.inr (Or.inl ⟨h₁, Or.inr h₂⟩)
    · -- u.val = 4, v.val = 2: symmetric.
      exact Or.inr (Or.inr (Or.inl ⟨h₂, Or.inr h₁⟩))
  unique := by
    intro u v w huv huw
    apply Fin.ext
    rcases huv with ⟨_, hv⟩ | ⟨_, hv⟩ <;>
    rcases huw with ⟨_, hw⟩ | ⟨_, hw⟩ <;> omega

/-! ## Refuting non-matchings

These are *not* matchings — usually because two "matching" edges share
a vertex, which violates `unique`. Use a wrapper-free predicate plus a
counterexample.
-/

/-- ★★  The set `{(0,1), (1,2)}` is *not* a matching on `P3` (vertex 1
    appears in both edges). State this as: there is no `Matching` whose
    `edge` predicate equals the proposed two-edge set.

    The cleanest formulation: assume such a matching `M` exists, and
    derive `(1 : Fin 3) = 0` (or some other contradiction) from
    `M.unique`. -/
example :
    ¬ ∃ (M : Matching P3),
      ∀ u v, M.edge u v ↔
        ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
         (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1)) := by
  intro ⟨M, hM⟩
  have h10 : M.edge (1 : Fin 3) 0 := (hM 1 0).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have h12 : M.edge (1 : Fin 3) 2 := (hM 1 2).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have heq : (0 : Fin 3) = 2 := M.unique h10 h12
  exact absurd (Fin.val_eq_of_eq heq) (by decide)

/-! ## Identifying partners and matched-ness -/

/-- ★★  In `MperfP4`, vertex `0`'s match-partner is `1`. -/
example {v : Fin 4} (h : MperfP4.edge 0 v) : v.val = 1 := by
  rcases h with ⟨_, hv⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all <;> omega

/-- ★★  In `M01_P4`, vertex `2` is unmatched. -/
example : M01_P4.IsUnmatched (2 : Fin 4) := by
  intro u h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- ★★  In `M01_P4`, vertex `3` is unmatched. -/
example : M01_P4.IsUnmatched (3 : Fin 4) := by
  intro u h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- ★★★  In `MperfP4`, no vertex is unmatched: it's a perfect matching. -/
example : ∀ v : Fin 4, ¬ MperfP4.IsUnmatched v := by
  intro v hv
  -- For each v, exhibit u such that MperfP4.edge u v.
  match v with
  | ⟨0, _⟩ => exact hv 1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | ⟨1, _⟩ => exact hv 0 (Or.inl ⟨rfl, rfl⟩)
  | ⟨2, _⟩ => exact hv 3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  | ⟨3, _⟩ => exact hv 2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-! ## Bonus: matchings via the empty matching -/

/-- ★  The empty matching has every vertex unmatched. -/
example (v : Fin 5) : (Matching.empty C5).IsUnmatched v := by
  intro u h; exact h.elim

/-- ★★  In the empty matching on `K4`, vertex `2` has no partner. -/
example {u : Fin 4} (h : (Matching.empty K4).edge u 2) : False := h.elim

end Hackathon.Toy.Exercises.Matchings
