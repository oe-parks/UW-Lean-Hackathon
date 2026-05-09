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

/-- ★  In `K3`, vertex `0` and `1` are adjacent.
    HINT: `K3 = complete (Fin 3)`; the edge predicate is `u ≠ v`. -/
example : K3.edge (0 : Fin 3) 1 := by sorry

/-- ★  In `K4`, vertex `0` is *not* adjacent to itself.
    HINT: this is `K4.edge_irrefl 0`. -/
example : ¬ K4.edge (0 : Fin 4) 0 := by sorry

/-- ★★  In `C5`, vertices `0` and `4` are adjacent (the wrap-around edge).
    HINT: unfold `cycleGraph`. The wrap-around case is the third or
    fourth disjunct: `0 = 0 ∧ 4 + 1 = 5`. -/
example : C5.edge (0 : Fin 5) 4 := by sorry

/-- ★★  In `P5`, vertices `0` and `2` are *not* adjacent.
    HINT: `pathGraph` only connects vertices whose values differ by 1. -/
example : ¬ P5.edge (0 : Fin 5) 2 := by sorry

/-- ★★  In `Star4`, the center `0` is adjacent to leaf `2`. -/
example : Star4.edge (0 : Fin 4) 2 := by sorry

/-- ★★  In `Star4`, leaves `1` and `2` are *not* adjacent. -/
example : ¬ Star4.edge (1 : Fin 4) 2 := by sorry

/-- ★★  In `Bowtie`, the shared vertex `2` is adjacent to `4`. -/
example : Bowtie.edge (2 : Fin 5) 4 := by sorry

/-- ★★★  In `K33`, vertices `1` (left side) and `4` (right side) are adjacent. -/
example : K33.edge (1 : Fin 6) 4 := by sorry

/-- ★★★  In `K33`, two left-side vertices `0` and `1` are *not* adjacent. -/
example : ¬ K33.edge (0 : Fin 6) 1 := by sorry

/-! ## Building matchings

Recall: a `Matching G` is a structure with five fields. Constructing it
is the proof that the chosen edges form a matching. Pattern from
`Worked.lean §2`.
-/

/-- ★★  The single-edge matching `{(0, 1)}` on `P4`. -/
def M01_P4 : Matching P4 where
  edge u v := (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0)
  edge_symm := by sorry
  edge_irrefl := by sorry
  edge_subgraph := by sorry
  unique := by sorry

/-- ★★  The single-edge matching `{(2, 3)}` on `P4`. -/
def M23_P4 : Matching P4 where
  edge u v := (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2)
  edge_symm := by sorry
  edge_irrefl := by sorry
  edge_subgraph := by sorry
  unique := by sorry

/-- ★★★  A perfect matching on `P4`: `{(0, 1), (2, 3)}`.
    HINT: pairs `(0,1)` and `(2,3)` are disjoint, so `unique` reduces
    to a small case analysis on `u.val ∈ {0, 1, 2, 3}`. -/
def MperfP4 : Matching P4 where
  edge u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2)
  edge_symm := by sorry
  edge_irrefl := by sorry
  edge_subgraph := by sorry
  unique := by sorry

/-- ★★★  A perfect matching on `K4`: `{(0, 1), (2, 3)}`. Note the
    underlying graph is different (`K4` has all 6 edges) but the
    matching's edge set is the same — the proofs differ only in
    `edge_subgraph`. -/
def MperfK4 : Matching K4 where
  edge u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 2)
  edge_symm := by sorry
  edge_irrefl := by sorry
  edge_subgraph := by
    -- HINT: `K4.edge u v = u ≠ v`. From the matching's case analysis
    -- you have `u.val ≠ v.val`, hence `u ≠ v` (use `Fin.ne_of_val_ne`).
    sorry
  unique := by sorry

/-- ★★  The single matching edge `(2, 4)` of the bow-tie. -/
def Mbowtie : Matching Bowtie where
  edge u v := (u.val = 2 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 2)
  edge_symm := by sorry
  edge_irrefl := by sorry
  edge_subgraph := by
    -- HINT: in `Bowtie`, the edge `2 — 4` lives in the second triangle.
    -- Look at the disjuncts of `Bowtie.edge`.
    sorry
  unique := by sorry

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
  -- HINT: From the matching, `M.edge 1 0` and `M.edge 1 2` both hold,
  -- so `M.unique` forces `(0 : Fin 3) = (2 : Fin 3)`, which is false.
  sorry

/-! ## Identifying partners and matched-ness -/

/-- ★★  In `MperfP4`, vertex `0`'s match-partner is `1`.
    Stated as: from `MperfP4.edge 0 v` we conclude `v.val = 1`. -/
example {v : Fin 4} (h : MperfP4.edge 0 v) : v.val = 1 := by
  -- HINT: `MperfP4.edge` is a 4-disjunct predicate. Three of the four
  -- disjuncts give `0.val = 1`, `0.val = 2`, `0.val = 3` — all false.
  -- Only one survives: `0.val = 0 ∧ v.val = 1`.
  sorry

/-- ★★  In `M01_P4`, vertex `2` is unmatched. -/
example : M01_P4.IsUnmatched (2 : Fin 4) := by sorry

/-- ★★  In `M01_P4`, vertex `3` is unmatched. -/
example : M01_P4.IsUnmatched (3 : Fin 4) := by sorry

/-- ★★★  In `MperfP4`, no vertex is unmatched: it's a perfect matching. -/
example : ∀ v : Fin 4, ¬ MperfP4.IsUnmatched v := by
  -- HINT: do case analysis on `v` with `Fin.cases` or `fin_cases v`.
  -- For each of the four vertices, exhibit a partner.
  sorry

/-! ## Bonus: matchings via the empty matching -/

/-- ★  The empty matching has every vertex unmatched.
    HINT: this is `Matching.empty_isUnmatched`. -/
example (v : Fin 5) : (Matching.empty C5).IsUnmatched v := by sorry

/-- ★★  In the empty matching on `K4`, vertex `2` has no partner. -/
example {u : Fin 4} (h : (Matching.empty K4).edge u 2) : False := by
  sorry

end Hackathon.Toy.Exercises.Matchings
