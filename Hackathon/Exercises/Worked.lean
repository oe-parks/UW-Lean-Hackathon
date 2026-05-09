import Hackathon.Exercises.Graphs

/-!
# Worked example — the Rosetta stone

A *complete* solution on the path graph `P4` (`0 — 1 — 2 — 3`).

We pick `P4`, not `P3`, because the smallest example of an
**augmenting path** needs at least four vertices: with matching
`M = {(1, 2)}` and walk `0 → 1 → 2 → 3` we get the alternating
sequence non-M, M, non-M, both endpoints exposed.

Every other exercise file references this file: when stuck, copy the
structure here and change the numbers.

## Recurring proof idioms

* **Name your edge proofs.** When you write `Walk.cons (Or.inl rfl) …`
  inline, Lean's elaborator can't pin down which `Or` disjunct
  `rfl` proves, and surrounding code becomes brittle. Define
  `theorem h01 : P4.edge 0 1 := Or.inl rfl` once and reuse it.
* **`abbrev` over `def` for walks.** `abbrev` walks unfold during
  defeq, so `apply Matching.IsAlternating.step` patterns the goal
  against `Walk.cons h₁ (Walk.cons h₂ q)` and pins the dependent
  arguments automatically.
* **Discharging arithmetic disjunctions.** Adjacency / matching
  predicates are usually `(a₁ ∧ b₁) ∨ (a₂ ∧ b₂)`. After
  `rcases h with …`, every case is killed by `omega`.
-/

namespace Hackathon.Toy.Worked

open Hackathon.Toy Graph

/-! ## §1. Adjacency in `P4` -/

/-- `P4` has the edge `0 — 1`. -/
theorem h01 : P4.edge (0 : Fin 4) 1 := Or.inl rfl

/-- `P4` has the edge `1 — 2`. -/
theorem h12 : P4.edge (1 : Fin 4) 2 := Or.inl rfl

/-- `P4` has the edge `2 — 3`. -/
theorem h23 : P4.edge (2 : Fin 4) 3 := Or.inl rfl

/-- `P4` does *not* have the edge `0 — 2`. -/
example : ¬ P4.edge (0 : Fin 4) 2 := by
  intro h
  rcases h with h | h <;> omega

/-! ## §2. The matching `M12 = {(1, 2)}` -/

/--
Constructing the `Matching` structure *is* the proof that this
sub-relation is a matching.
-/
def M12 : Matching P4 where
  edge u v := (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1)
  edge_symm := by
    intro u v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂, h₁⟩
    · exact Or.inl ⟨h₂, h₁⟩
  edge_irrefl := by
    intro v h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
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

/-! ## §3. Unmatched vertices -/

/-- Vertex `0` is unmatched in `M12`. -/
example : M12.IsUnmatched (0 : Fin 4) := by
  intro u h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- Vertex `3` is unmatched in `M12`. -/
example : M12.IsUnmatched (3 : Fin 4) := by
  intro u h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-! ## §4. A walk -/

/-- The walk `0 → 1 → 2 → 3` in `P4`. -/
abbrev w0123 : Walk P4 (0 : Fin 4) 3 :=
  Walk.cons h01 (Walk.cons h12 (Walk.cons h23 Walk.nil))

/-! ## §5. The walk is a path -/

example : w0123.IsPath := by
  change w0123.support.Nodup
  decide

/-! ## §6. Alternating against the matching -/

/--
`w0123` is `M12`-alternating. Length 3 means we apply `step` *twice*,
then close with `single`. Each `step` produces an `hflip` subgoal (the
iff between consecutive edges) and an `hrest` subgoal (alternating on
the tail).
-/
example : M12.IsAlternating w0123 := by
  apply Matching.IsAlternating.step
  · -- hflip₁ : `(0,1) ∈ M ↔ ¬ (1,2) ∈ M`. Edge `(0,1)` is *not* in M, edge `(1,2)` *is*.
    constructor
    · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · intro h; exact absurd (Or.inl ⟨rfl, rfl⟩) h
  · -- hrest₁ : alternating on `cons h12 (cons h23 nil)`.
    apply Matching.IsAlternating.step
    · -- hflip₂ : `(1,2) ∈ M ↔ ¬ (2,3) ∈ M`. Edge `(1,2)` *is* in M, `(2,3)` is not.
      constructor
      · intro _h₁ h₂; rcases h₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · intro _h; exact Or.inl ⟨rfl, rfl⟩
    · apply Matching.IsAlternating.single

/-! ## §7. The augmenting-path proof -/

/-- **The showcase.** `w0123` is `M12`-augmenting. -/
example : Walk.IsAugmenting M12 w0123 where
  -- (1) Non-empty: length 3 > 0.
  nonEmpty := by decide
  -- (2) Path.
  isPath := by change w0123.support.Nodup; decide
  -- (3) Alternating — same proof as in §6.
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
  -- (4) First edge `(0, 1)` is not in `M12`.
  firstNotInM := by
    apply Matching.firstEdgeNotInM.here
    intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  -- (5) Start `0` is unmatched.
  startUnmatched := by
    intro u h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  -- (6) End `3` is unmatched.
  endUnmatched := by
    intro u h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

end Hackathon.Toy.Worked
