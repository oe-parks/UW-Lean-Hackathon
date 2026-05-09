import Hackathon.Graph.Toy.Matching

/-!
# Walks and augmenting paths in the toy graph layer

A `Walk G u v` is a sequence of edges in `G` from `u` to `v`.

* `Walk` — inductive: `nil` (length-0 walk) or `cons` (prepend an edge).
* `length`, `support`, `edges`.
* `IsPath` — no repeated vertex.
* `Matching.IsAlternating` — inductive predicate; consecutive edges flip
  in/out of `M`.
* `Matching.firstEdgeNotInM` — the first edge of the walk is not in `M`.
* `Walk.IsAugmenting` — non-empty path, alternating, with both
  endpoints unmatched and first edge non-`M`.

`IsAlternating` and `firstEdgeNotInM` are stated as `inductive` rather
than recursive `def`s: this means proofs are built by applying their
constructors directly (`.nil`, `.single`, `.cons` for alternating;
`.nil`, `.cons` for first-edge), which avoids the defeq /
pattern-unfolding pain you hit with the recursive form.
-/

namespace Hackathon.Toy

universe u

variable {V : Type u}

/-- A walk in `G` from `u` to `v`. -/
inductive Walk (G : Graph V) : V → V → Type u
  /-- Empty walk: stay at `v`. -/
  | nil  {v : V} : Walk G v v
  /-- Step along an edge `u → v`, then continue. -/
  | cons {u v w : V} (h : G.edge u v) (p : Walk G v w) : Walk G u w

namespace Walk

variable {G : Graph V}

/-- Number of edges in the walk. -/
def length : {u v : V} → Walk G u v → ℕ
  | _, _, .nil       => 0
  | _, _, .cons _ p  => p.length + 1

/-- Vertices the walk visits, including the endpoints. -/
def support : {u v : V} → Walk G u v → List V
  | _, v, .nil      => [v]
  | u, _, .cons _ p => u :: p.support

/-- Consecutive vertex pairs (edges) along the walk. -/
def edges : {u v : V} → Walk G u v → List (V × V)
  | _, _, .nil               => []
  | u, _, .cons (v := v) _ p => (u, v) :: p.edges

@[simp] theorem length_nil {v : V} : (Walk.nil : Walk G v v).length = 0 := rfl

@[simp] theorem length_cons {u v w : V} (h : G.edge u v) (p : Walk G v w) :
    (Walk.cons h p).length = p.length + 1 := rfl

@[simp] theorem support_nil {v : V} : (Walk.nil : Walk G v v).support = [v] := rfl

@[simp] theorem support_cons {u v w : V} (h : G.edge u v) (p : Walk G v w) :
    (Walk.cons h p).support = u :: p.support := rfl

@[simp] theorem edges_nil {v : V} : (Walk.nil : Walk G v v).edges = [] := rfl

@[simp] theorem edges_cons {u v w : V} (h : G.edge u v) (p : Walk G v w) :
    (Walk.cons h p).edges = (u, v) :: p.edges := rfl

/-- A walk is a *path* if its support has no repeats. -/
def IsPath {u v : V} (w : Walk G u v) : Prop := w.support.Nodup

@[simp] theorem isPath_def {u v : V} (w : Walk G u v) :
    w.IsPath ↔ w.support.Nodup := Iff.rfl

end Walk

namespace Matching

variable {G : Graph V}

/--
A walk is *M-alternating* iff every two consecutive edges differ in
their `M`-membership. We define this inductively:

* `nil`: the empty walk is alternating.
* `single h`: a one-edge walk is alternating.
* `cons h₁ h₂ q hflip hrest`: prepending edge `h₁` to an alternating
  walk starting with edge `h₂` works when `(h₁ ∈ M) ↔ ¬ (h₂ ∈ M)`.
-/
inductive IsAlternating (M : Matching G) : {u v : V} → Walk G u v → Prop where
  /-- Empty walks are alternating. -/
  | nil {v : V} : IsAlternating M (Walk.nil : Walk G v v)
  /-- One-edge walks are alternating. -/
  | single {u v : V} (h : G.edge u v) : IsAlternating M (Walk.cons h Walk.nil)
  /-- Extend by one edge with flipped membership. -/
  | step {u v w x : V} (h₁ : G.edge u v) (h₂ : G.edge v w) (q : Walk G w x)
      (hflip : M.edge u v ↔ ¬ M.edge v w)
      (hrest : IsAlternating M (Walk.cons h₂ q)) :
      IsAlternating M (Walk.cons h₁ (Walk.cons h₂ q))

/-- The first edge of a walk is *not* in the matching (vacuous on `nil`). -/
inductive firstEdgeNotInM (M : Matching G) : {u v : V} → Walk G u v → Prop where
  /-- Vacuously true for empty walks. -/
  | nil {v : V} : firstEdgeNotInM M (Walk.nil : Walk G v v)
  /-- For non-empty walks, the first edge `(u, v)` must not be in `M`. -/
  | here {u v w : V} (h : G.edge u v) (p : Walk G v w) (notIn : ¬ M.edge u v) :
      firstEdgeNotInM M (Walk.cons h p)

end Matching

namespace Walk

variable {G : Graph V}

/--
`w : Walk G u v` is *M-augmenting* iff
1. it has at least one edge,
2. it is a path,
3. it is `M`-alternating,
4. its first edge is *not* in `M`,
5. both endpoints are unmatched.
-/
structure IsAugmenting (M : Matching G) {u v : V} (w : Walk G u v) : Prop where
  /-- Non-trivial: at least one edge. -/
  nonEmpty       : 0 < w.length
  /-- Walk is a (simple) path. -/
  isPath         : w.IsPath
  /-- Edges alternate in/out of `M`. -/
  alternating    : M.IsAlternating w
  /-- First edge of the walk is not in `M`. -/
  firstNotInM    : M.firstEdgeNotInM w
  /-- Start endpoint is unmatched. -/
  startUnmatched : M.IsUnmatched u
  /-- End endpoint is unmatched. -/
  endUnmatched   : M.IsUnmatched v

end Walk

end Hackathon.Toy
