import Hackathon.Graph.Toy.Walk
import Hackathon.Exercises.Graphs

/-!
# Naive BFS reachability — complete proof, optimize with autoresearch

`ReachInSteps G u v n` : v is reachable from u via a walk of length ≤ n.

The proofs below are correct but use common slow patterns:
- bare `simp` instead of `simp only [...]` — tries all simp lemmas
- `omega` where `Nat.le_trans` or `le_refl _` would be faster
- `by exact t` tactic wrappers where direct term proofs elaborate faster
- `simp [...]` + `omega` where a targeted `rw` + arithmetic step suffices

Run `python scripts/autoresearch.py --optimize Hackathon/Graph/BFS.lean`
to let autoresearch find faster proof alternatives.
-/

-- Walk utilities must live in Hackathon.Toy so dot-notation resolves.
namespace Hackathon.Toy

universe u
variable {V : Type u} {G : Graph V}

/-- Concatenate two walks. -/
def Walk.append : ∀ {u v w : V}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil,      q => q
  | _, _, _, .cons h p, q => .cons h (Walk.append p q)

@[simp] theorem Walk.append_nil {u w : V} (q : Walk G u w) :
    (Walk.nil : Walk G u u).append q = q := rfl

@[simp] theorem Walk.append_cons {u v x w : V}
    (h : G.edge u v) (p : Walk G v x) (q : Walk G x w) :
    (Walk.cons h p).append q = Walk.cons h (p.append q) := rfl

/-- Length distributes over concatenation. -/
theorem Walk.append_length {u v w : V} (p : Walk G u v) (q : Walk G v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil        => simp          -- slow: bare simp (target: simp only + Nat.zero_add)
  | cons h p ih => simp [ih]; omega  -- slow: simp then omega (target: simp only + omega)

/-- Reverse a walk using symmetry of edges. -/
def Walk.reverse : ∀ {u v : V}, Walk G u v → Walk G v u
  | _, _, .nil      => .nil
  | _, _, .cons h p => p.reverse.append (.cons (G.edge_symm h) .nil)

-- simp lemmas for reverse so that reverse_length can use simp
@[simp] theorem Walk.reverse_nil {v : V} :
    (Walk.nil : Walk G v v).reverse = Walk.nil := rfl

@[simp] theorem Walk.reverse_cons {u v w : V} (h : G.edge u v) (p : Walk G v w) :
    (Walk.cons h p).reverse = p.reverse.append (.cons (G.edge_symm h) .nil) := rfl

/-- Reversing preserves length. -/
theorem Walk.reverse_length {u v : V} (p : Walk G u v) :
    p.reverse.length = p.length := by
  induction p with
  | nil        => simp                         -- slow: bare simp
  | cons h p ih => simp [Walk.append_length, ih]  -- slow: simp with args

end Hackathon.Toy

namespace Hackathon.BFS

open Hackathon.Toy Graph

universe u
variable {V : Type u} {G : Graph V}

/-- `v` is reachable from `u` in at most `n` steps. -/
def ReachInSteps (G : Graph V) (u v : V) (n : ℕ) : Prop :=
  ∃ w : Walk G u v, w.length ≤ n

-- ── Core BFS lemmas ───────────────────────────────────────────────────────────

/-- Every vertex reaches itself in 0 steps. -/
lemma reach_refl (v : V) : ReachInSteps G v v 0 :=
  ⟨Walk.nil, by simp⟩             -- slow: simp (target: Nat.le_refl 0)

/-- An adjacent vertex is reachable in 1 step. -/
lemma reach_adj {u v : V} (h : G.edge u v) : ReachInSteps G u v 1 :=
  ⟨Walk.cons h Walk.nil, by simp⟩ -- slow: simp (target: Nat.le_refl 1)

/-- Monotonicity: reachable in n steps ⟹ reachable in m ≥ n steps. -/
lemma reach_mono {u v : V} {n m : ℕ}
    (h : ReachInSteps G u v n) (hnm : n ≤ m) : ReachInSteps G u v m := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by omega⟩             -- slow: omega (target: Nat.le_trans hw hnm)

/-- Transitivity: compose walks through an intermediate vertex. -/
lemma reach_trans {u v w : V} {m n : ℕ}
    (huv : ReachInSteps G u v m) (hvw : ReachInSteps G v w n) :
    ReachInSteps G u w (m + n) := by
  obtain ⟨pw, hpw⟩ := huv
  obtain ⟨qw, hqw⟩ := hvw
  refine ⟨pw.append qw, ?_⟩
  simp [Walk.append_length]        -- slow: simp (target: rw [Walk.append_length])
  omega

/-- Symmetry: reachability is symmetric in undirected graphs. -/
lemma reach_symm {u v : V} {n : ℕ}
    (h : ReachInSteps G u v n) : ReachInSteps G v u n := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse,
    by simp [Walk.reverse_length, hw]⟩ -- slow: simp (target: Walk.reverse_length w ▸ hw)

/-- Extend a reach by one adjacent step. -/
lemma reach_extend {u v w : V} {m : ℕ}
    (huv : ReachInSteps G u v m) (hvw : G.edge v w) :
    ReachInSteps G u w (m + 1) :=
  reach_trans huv (reach_adj hvw)

-- ── P4 edge witnesses (fix endpoints so Or.inl rfl elaborates correctly) ──────
-- These mirror the pattern from Worked.lean.
private theorem e01 : P4.edge (0 : Fin 4) 1 := Or.inl rfl
private theorem e12 : P4.edge (1 : Fin 4) 2 := Or.inl rfl
private theorem e23 : P4.edge (2 : Fin 4) 3 := Or.inl rfl

-- ── Concrete reachability facts ───────────────────────────────────────────────
-- Slow pattern: tactic-mode proofs with `apply` + `exact`.
-- Tactic elaboration is measurably slower than equivalent term proofs.
-- Fast alternative: direct term like `reach_adj e01` or `⟨Walk.cons e01 Walk.nil, le_refl _⟩`.

/-- In P4: 0 → 1 in 1 step. -/
example : ReachInSteps P4 (0 : Fin 4) 1 1 := by
  apply reach_adj           -- slow: tactic mode
  exact e01

/-- In P4: 1 → 2 in 1 step. -/
example : ReachInSteps P4 (1 : Fin 4) 2 1 := by
  apply reach_adj
  exact e12

/-- In P4: 2 → 3 in 1 step. -/
example : ReachInSteps P4 (2 : Fin 4) 3 1 := by
  apply reach_adj
  exact e23

/-- In P4: 0 → 2 in 2 steps (via vertex 1). -/
example : ReachInSteps P4 (0 : Fin 4) 2 2 := by
  change ReachInSteps P4 0 2 (1 + 1)  -- slow: tactic mode + change for sum
  apply reach_trans
  · exact reach_adj e01
  · exact reach_adj e12

/-- In P4: 0 → 3 in 3 steps. -/
example : ReachInSteps P4 (0 : Fin 4) 3 3 := by
  change ReachInSteps P4 0 3 (1 + (1 + 1))
  apply reach_trans
  · exact reach_adj e01
  · change ReachInSteps P4 1 3 (1 + 1)
    apply reach_trans
    · exact reach_adj e12
    · exact reach_adj e23

/-- In P4: BFS from 3 reaches 0 in 3 steps (symmetry). -/
example : ReachInSteps P4 (3 : Fin 4) 0 3 := by
  exact reach_symm (reach_trans (reach_adj e01) (reach_trans (reach_adj e12) (reach_adj e23)))

end Hackathon.BFS
