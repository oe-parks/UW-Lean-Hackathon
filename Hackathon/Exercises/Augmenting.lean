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
example : p4_walk.length = 3 := rfl

/-- ★  `p5_walk` has length 4. -/
example : p5_walk.length = 4 := rfl

/-- ★★  `c4_loop` has length 4. -/
example : c4_loop.length = 4 := rfl

/-! ## Path-ness -/

/-- ★★  `p4_walk` is a path. -/
example : p4_walk.IsPath := by
  change p4_walk.support.Nodup
  decide

/-- ★★  `p5_walk` is a path. -/
example : p5_walk.IsPath := by
  change p5_walk.support.Nodup
  decide

/-- ★★  `c4_loop` is *not* a path: it revisits vertex `0`. -/
example : ¬ c4_loop.IsPath := by
  intro h
  change c4_loop.support.Nodup at h
  exact absurd h (by decide)

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

/-- ★★  `p4_walk` is `M_P4_12`-alternating. -/
example : M_P4_12.IsAlternating p4_walk := by
  apply Matching.IsAlternating.step
  · constructor
    · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · intro h; exact absurd (Or.inl ⟨rfl, rfl⟩) h
  · apply Matching.IsAlternating.step
    · constructor
      · intro _ h₂; rcases h₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · intro _; exact Or.inl ⟨rfl, rfl⟩
    · apply Matching.IsAlternating.single

/-- ★★★  `p5_walk` is `M_P5_12_34`-alternating. -/
example : M_P5_12_34.IsAlternating p5_walk := by
  apply Matching.IsAlternating.step
  · constructor
    · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · intro h; exact absurd (Or.inl ⟨rfl, rfl⟩) h
  · apply Matching.IsAlternating.step
    · constructor
      · intro _ h₂; rcases h₂ with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · intro _; exact Or.inl ⟨rfl, rfl⟩
    · apply Matching.IsAlternating.step
      · constructor
        · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        · intro h; exact absurd (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h
      · apply Matching.IsAlternating.single

/-! ## Augmenting paths

These are the showcase exercises — pattern from `Worked.lean §7`.
-/

/-- ★★★  `p4_walk` is an `M_P4_12`-augmenting path. -/
example : Walk.IsAugmenting M_P4_12 p4_walk where
  nonEmpty := by decide
  isPath := by change p4_walk.support.Nodup; decide
  alternating := by
    apply Matching.IsAlternating.step
    · constructor
      · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · intro h; exact absurd (Or.inl ⟨rfl, rfl⟩) h
    · apply Matching.IsAlternating.step
      · constructor
        · intro _ h₂; rcases h₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        · intro _; exact Or.inl ⟨rfl, rfl⟩
      · apply Matching.IsAlternating.single
  firstNotInM := by
    apply Matching.firstEdgeNotInM.here
    intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  startUnmatched := by
    intro u h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  endUnmatched := by
    intro u h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- ★★★  `p5_walk` is *not* `M_P5_12_34`-augmenting (vertex 4 is matched). -/
example : ¬ Walk.IsAugmenting M_P5_12_34 p5_walk := by
  intro h
  -- endUnmatched would say 4 has no partner, but (3, 4) is in M.
  exact h.endUnmatched 3 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-! ## Refuting augmenting paths -/

/-- ★★  The walk in `C5` from `0` along `0 → 1 → 2 → 3 → 4 → 0` is *not*
    a path (it revisits `0`), so it cannot be augmenting. -/
example :
    let w : Walk C5 (0 : Fin 5) 0 :=
      Walk.cons c5_h01 (Walk.cons c5_h12 (Walk.cons c5_h23 (Walk.cons c5_h34
        (Walk.cons (⟨by decide, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩) Walk.nil))))
    ¬ Walk.IsAugmenting (Matching.empty C5) w := by
  intro w h
  -- The walk's support is [0, 1, 2, 3, 4, 0] which has duplicates.
  have hpath : w.support.Nodup := h.isPath
  exact absurd hpath (by decide)

/-- ★★  The walk `0 → 1` in `P4`, against the **empty** matching, *is*
    augmenting (length 1, both endpoints unmatched, first edge not in M). -/
example :
    Walk.IsAugmenting (Matching.empty P4) (Walk.cons p4_h01 Walk.nil) where
  nonEmpty := by decide
  isPath := by
    change (Walk.cons p4_h01 Walk.nil).support.Nodup
    decide
  alternating := Matching.IsAlternating.single _
  firstNotInM := Matching.firstEdgeNotInM.here _ _ (fun h => h.elim)
  startUnmatched := fun u h => h.elim
  endUnmatched := fun u h => h.elim

/-! ## Conceptual lemmas -/

/-- ★★★  An augmenting walk has length ≥ 1. -/
example {V : Type*} {G : Graph V} {M : Matching G} {u v : V}
    {w : Walk G u v} (h : Walk.IsAugmenting M w) :
    1 ≤ w.length := h.nonEmpty

/-- ★★★  If a walk is augmenting, both its endpoints are unmatched. -/
example {V : Type*} {G : Graph V} {M : Matching G} {u v : V}
    {w : Walk G u v} (h : Walk.IsAugmenting M w) :
    M.IsUnmatched u ∧ M.IsUnmatched v :=
  ⟨h.startUnmatched, h.endUnmatched⟩

end Hackathon.Toy.Exercises.Augmenting
