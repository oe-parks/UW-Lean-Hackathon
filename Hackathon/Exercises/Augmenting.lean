import Hackathon.Exercises.Worked

/-!
# Exercises: walks, paths, augmenting paths

The pattern from `Worked.lean` carries over directly. In particular:

* Define edge proofs by name (e.g. `theorem h01 : G.edge 0 1 := …`).
* Make walks `abbrev`s so `apply Matching.IsAlternating.step` patterns
  the goal correctly.
* Use `Matching.IsAlternating.step / .single / .nil` to build
  alternating proofs; `Matching.firstEdgeNotInM.here` for the
  "first edge not in M" condition.

Difficulty:  ★ easy   ★★ moderate   ★★★ harder
-/

namespace Hackathon.Toy.Exercises.Augmenting

open Hackathon.Toy Graph

/-! ## Edge proofs we'll reuse -/

theorem p4_h01 : P4.edge (0 : Fin 4) 1 := Or.inl rfl
theorem p4_h12 : P4.edge (1 : Fin 4) 2 := Or.inl rfl
theorem p4_h23 : P4.edge (2 : Fin 4) 3 := Or.inl rfl

theorem p5_h01 : P5.edge (0 : Fin 5) 1 := Or.inl rfl
theorem p5_h12 : P5.edge (1 : Fin 5) 2 := Or.inl rfl
theorem p5_h23 : P5.edge (2 : Fin 5) 3 := Or.inl rfl
theorem p5_h34 : P5.edge (3 : Fin 5) 4 := Or.inl rfl

theorem c4_h01 : C4.edge (0 : Fin 4) 1 := ⟨by decide, Or.inl rfl⟩
theorem c4_h12 : C4.edge (1 : Fin 4) 2 := ⟨by decide, Or.inl rfl⟩
theorem c4_h23 : C4.edge (2 : Fin 4) 3 := ⟨by decide, Or.inl rfl⟩
theorem c4_h30 : C4.edge (3 : Fin 4) 0 := ⟨by decide, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

theorem c5_h01 : C5.edge (0 : Fin 5) 1 := ⟨by decide, Or.inl rfl⟩
theorem c5_h12 : C5.edge (1 : Fin 5) 2 := ⟨by decide, Or.inl rfl⟩
theorem c5_h23 : C5.edge (2 : Fin 5) 3 := ⟨by decide, Or.inl rfl⟩
theorem c5_h34 : C5.edge (3 : Fin 5) 4 := ⟨by decide, Or.inl rfl⟩

/-! ## Building walks -/

/-- ★  The walk `0 → 1 → 2 → 3` in `P4`. -/
abbrev p4_walk : Walk P4 (0 : Fin 4) 3 :=
  Walk.cons p4_h01 (Walk.cons p4_h12 (Walk.cons p4_h23 Walk.nil))

/-- ★  The walk `0 → 1 → 2 → 3 → 4` in `P5`. -/
abbrev p5_walk : Walk P5 (0 : Fin 5) 4 :=
  Walk.cons p5_h01 (Walk.cons p5_h12 (Walk.cons p5_h23 (Walk.cons p5_h34 Walk.nil)))

/-- ★  The closed walk `0 → 1 → 2 → 3 → 0` in `C4`. -/
abbrev c4_loop : Walk C4 (0 : Fin 4) 0 :=
  Walk.cons c4_h01 (Walk.cons c4_h12 (Walk.cons c4_h23 (Walk.cons c4_h30 Walk.nil)))

/-! ## Length and support -/

/-- ★  `p4_walk` has length 3. -/
example : p4_walk.length = 3 := by sorry

/-- ★  `p5_walk` has length 4. -/
example : p5_walk.length = 4 := by sorry

/-- ★★  `c4_loop` has length 4. -/
example : c4_loop.length = 4 := by sorry

/-! ## Path-ness -/

/-- ★★  `p4_walk` is a path.
    HINT: pattern from `Worked.lean §5`. -/
example : p4_walk.IsPath := by sorry

/-- ★★  `p5_walk` is a path. -/
example : p5_walk.IsPath := by sorry

/-- ★★  `c4_loop` is *not* a path: it revisits vertex `0`.
    HINT: prove that `[0, 1, 2, 3, 0].Nodup` is false. -/
example : ¬ c4_loop.IsPath := by sorry

/-! ## Matchings used by the augmenting-path exercises -/

/-- The matching `M = {(1, 2)}` on `P4`. (Same shape as `Worked.M12`.) -/
def M_P4_12 : Matching P4 where
  edge u v := (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1)
  edge_symm := by
    intro u v h; rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨b, a⟩
    · exact Or.inl ⟨b, a⟩
  edge_irrefl := by
    intro v h; rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  edge_subgraph := by
    intro u v h; rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  unique := by
    intro u v w h₁ h₂; apply Fin.ext
    rcases h₁ with ⟨_, a⟩ | ⟨_, a⟩ <;>
    rcases h₂ with ⟨_, b⟩ | ⟨_, b⟩ <;> omega

/-- The matching `M = {(1, 2), (3, 4)}` on `P5`. -/
def M_P5_12_34 : Matching P5 where
  edge u v :=
    (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1) ∨
    (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 3)
  edge_symm := by
    intro u v h
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr (Or.inl ⟨b, a⟩)
    · exact Or.inl ⟨b, a⟩
    · exact Or.inr (Or.inr (Or.inr ⟨b, a⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨b, a⟩))
  edge_irrefl := by
    intro v h
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  edge_subgraph := by
    intro u v h
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  unique := by
    intro u v w h₁ h₂; apply Fin.ext
    rcases h₁ with ⟨_, a⟩ | ⟨_, a⟩ | ⟨_, a⟩ | ⟨_, a⟩ <;>
    rcases h₂ with ⟨_, b⟩ | ⟨_, b⟩ | ⟨_, b⟩ | ⟨_, b⟩ <;> omega

/-! ## Alternating proofs -/

/-- ★★  `p4_walk` is `M_P4_12`-alternating.
    HINT: pattern from `Worked.lean §6`. Use `step` once, then `step`
    again, then `single`. -/
example : M_P4_12.IsAlternating p4_walk := by sorry

/-- ★★★  `p5_walk` is `M_P5_12_34`-alternating.
    HINT: three applications of `step`, then `single`. The four
    consecutive edge-pairs all flip M-membership:
    `(0,1) ∉ M`, `(1,2) ∈ M`, `(2,3) ∉ M`, `(3,4) ∈ M`. -/
example : M_P5_12_34.IsAlternating p5_walk := by sorry

/-! ## Augmenting paths

These are the showcase exercises — pattern from `Worked.lean §7`.
-/

/-- ★★★  `p4_walk` is an `M_P4_12`-augmenting path. -/
example : Walk.IsAugmenting M_P4_12 p4_walk := by sorry

/-- ★★★  `p5_walk` is an `M_P5_12_34`-augmenting path.

Note: this matching covers `{1,2,3,4}`; only vertex `0` is exposed. So
both endpoints of `p5_walk` (vertices `0` and `4`) are unmatched —
wait, vertex `4` *is* matched (to `3`)! Re-check: the walk `0→1→2→3→4`
ends at `4`, which is matched. So this walk is **not** augmenting.

Replace this exercise with a refutation: prove that the walk is
*not* augmenting. -/
example : ¬ Walk.IsAugmenting M_P5_12_34 p5_walk := by
  -- HINT: the proof is by contradiction. Extract `endUnmatched` from
  -- the augmenting structure and derive `M_P5_12_34.IsUnmatched 4`,
  -- which is false because `M_P5_12_34.edge 3 4` holds.
  sorry

/-! ## Refuting augmenting paths -/

/-- ★★  The walk in `C5` from `0` along `0 → 1 → 2 → 3 → 4 → 0` is *not*
    a path (it revisits `0`), so it cannot be augmenting. -/
example :
    let w : Walk C5 (0 : Fin 5) 0 :=
      Walk.cons c5_h01 (Walk.cons c5_h12 (Walk.cons c5_h23 (Walk.cons c5_h34
        (Walk.cons (by
          -- HINT: `(4, 0)` is the wrap-around edge of `C5`. Build the proof.
          sorry) Walk.nil))))
    ¬ Walk.IsAugmenting (Matching.empty C5) w := by
  sorry

/-- ★★  The walk `0 → 1` in `P4`, against the **empty** matching, *is*
    augmenting (length 1, both endpoints unmatched, first edge not in
    M).
    HINT: an augmenting walk doesn't have to be long. Length-1 walks
    are augmenting iff both endpoints are unmatched. Use
    `IsAlternating.single` for the alternating part. -/
example :
    Walk.IsAugmenting (Matching.empty P4) (Walk.cons p4_h01 Walk.nil) := by
  sorry

/-! ## Conceptual lemmas -/

/-- ★★★  An augmenting walk has length ≥ 1.
    HINT: it's literally the `nonEmpty` field. -/
example {V : Type*} {G : Graph V} {M : Matching G} {u v : V}
    {w : Walk G u v} (h : Walk.IsAugmenting M w) :
    1 ≤ w.length := by sorry

/-- ★★★  If a walk is augmenting, both its endpoints are unmatched.
    HINT: `startUnmatched` and `endUnmatched`. -/
example {V : Type*} {G : Graph V} {M : Matching G} {u v : V}
    {w : Walk G u v} (h : Walk.IsAugmenting M w) :
    M.IsUnmatched u ∧ M.IsUnmatched v := by sorry

end Hackathon.Toy.Exercises.Augmenting
