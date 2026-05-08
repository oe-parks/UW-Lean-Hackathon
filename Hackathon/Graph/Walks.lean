import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Paths

/-
# Walks and paths — practice on Mathlib's API

We now use Mathlib's `SimpleGraph.Walk` and `SimpleGraph.Walk.IsPath`
directly. This file collects practice lemmas that exercise the API.

Reference (Mathlib): `Mathlib.Combinatorics.SimpleGraph.Walk`,
`Mathlib.Combinatorics.SimpleGraph.Path`.
-/

namespace Hackathon

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/- ## Walk basics -/

/-- ★  The reverse of a `nil` walk is `nil`. -/
example (v : V) : (Walk.nil : G.Walk v v).reverse = Walk.nil := by
  -- HINT: `simp` with `Walk.reverse_nil`.
  sorry

/-- ★  A walk and its reverse have the same length. -/
example {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  -- HINT: `Walk.length_reverse`.
  sorry

/-- ★★  Concatenating a walk with `nil` does not change its length. -/
example {u v : V} (p : G.Walk u v) : (p.append Walk.nil).length = p.length := by
  -- HINT: induction on `p`, or use `Walk.append_nil` + `simp`.
  sorry

/-- ★★  Length of `append` is the sum of lengths. -/
example {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  -- HINT: `Walk.length_append`.
  sorry

/- ## Paths -/

/-- ★  Every path is a walk. (Trivial — paths are bundled walks.) -/
example {u v : V} (p : G.Path u v) : G.Walk u v := p.val

/-- ★★  A walk of length 0 from `u` to `v` forces `u = v`. -/
example {u v : V} (p : G.Walk u v) (h : p.length = 0) : u = v := by
  -- HINT: `cases p`. The `cons` case has `length ≥ 1`, contradicting `h`.
  sorry

/-- ★★★  If `p : G.Walk u v` is a path, so is `p.reverse`. -/
example {u v : V} (p : G.Walk u v) (hp : p.IsPath) : p.reverse.IsPath := by
  -- HINT: `Walk.IsPath.reverse`.
  sorry

end Hackathon
