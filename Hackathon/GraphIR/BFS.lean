import Hackathon.GraphIR.Examples
import Mathlib.Tactic

/-!
# Breadth-first search in GraphIR

`bfsProgram` computes, given a source vertex `s`, an association map
from each reachable vertex `v` to the shortest path length from `s`.

Implementation (functional / SSA, using mutual recursion):

```
bfs_step(queue, dist) =
  match queue with
  | []          => dist                             // done
  | (u, d) :: rest =>
      process_ns(rest, dist, neighbors(u), d)

process_ns(queue, dist, ns, d) =
  match ns with
  | []      => bfs_step(queue, dist)
  | n :: rest =>
      if isSome(map_lookup(n, dist))                // already visited
      then process_ns(queue, dist, rest, d)
      else
        let dist'  = map_insert(n, d+1, dist)
        let queue' = list_append(queue, [(n, d+1)])
        process_ns(queue', dist', rest, d)

bfs(s) =
  bfs_step([(s, 0)], map_insert(s, 0, []))
```

We expose three things:

* `bfsProgram` — the IR program, runnable via `#eval`.
* `runBFS` — convenience wrapper that takes a source vertex literal.
* A correctness scaffold: `theorem bfs_correct` stating the headline
  result, with the proof's deeper parts left as `sorry` for later.
-/

namespace Hackathon.GraphIR.BFS

open Hackathon.GraphIR Examples

/-! ## The BFS program -/

/-- The mutually-recursive `bfs_step` and `process_ns`, plus the
    top-level `bfs(s)` wrapper. -/
def bfsFuns : List FunDecl :=
  [ { name := "bfs_step"
      params := ["queue", "dist"]
      body :=
        .matchList (v "queue")
          (v "dist")                           -- queue empty → return dist
          "head" "rest"
          (.matchPair (v "head") "u" "d"
            (c "process_ns"
              [ v "rest"
              , v "dist"
              , c "graph_neighbors" [v "u"]
              , v "d"
              ]))
    }
  , { name := "process_ns"
      params := ["queue", "dist", "ns", "d"]
      body :=
        .matchList (v "ns")
          (c "bfs_step" [v "queue", v "dist"])    -- no more neighbors
          "n" "rest"
          (.ite
            (c "opt_isSome" [c "map_lookup" [v "n", v "dist"]])
              -- already visited
              (c "process_ns" [v "queue", v "dist", v "rest", v "d"])
              -- new: enqueue and record distance d+1
              (lt "d1" (c "nat_succ" [v "d"])
              (lt "dist1" (c "map_insert" [v "n", v "d1", v "dist"])
              (lt "queue1" (c "list_append"
                              [ v "queue"
                              , c "list_cons"
                                  [c "pair_mk" [v "n", v "d1"], .nilE]
                              ])
              (c "process_ns"
                [v "queue1", v "dist1", v "rest", v "d"])))))
    }
  , { name := "bfs"
      params := ["s"]
      body :=
        lt "init_pair" (c "pair_mk" [v "s", nat' 0])
        (lt "init_queue" (c "list_cons" [v "init_pair", .nilE])
        (lt "init_dist" (c "map_insert" [v "s", nat' 0, .nilE])
        (c "bfs_step" [v "init_queue", v "init_dist"])))
    }
  ]

/-- The BFS program, run from vertex `s`, returns its distance map. -/
def bfsProgram (sIdx : Nat) : Program where
  funs := bfsFuns
  main := c "bfs" [vert' sIdx]

/-! ## Run BFS on the example graphs -/

#eval Interp.run (cfg3 k3Ctx) 1000 (bfsProgram 0)
-- triangle K3 from vertex 0: every other vertex at distance 1
-- ⇒ (some) [(v2, 1), (v1, 1), (v0, 0)]   (order may vary)

#eval Interp.run (cfg4 p4Ctx) 1000 (bfsProgram 0)
-- path 0—1—2—3 from vertex 0: distances 0, 1, 2, 3.
-- ⇒ (some) [(v3, 3), (v2, 2), (v1, 1), (v0, 0)]

#eval Interp.run (cfg4 p4Ctx) 1000 (bfsProgram 2)
-- path from vertex 2: distances 2, 1, 0, 1 for v0, v1, v2, v3.

/-! ## A reference BFS implementation in Lean

To state and prove correctness without unfolding the entire interpreter,
we lift the IR program into a regular Lean function that does the same
thing. Then the correctness theorem has two halves:

1. `bfsLean` is correct (uses graph theory of `Toy.Walk`).
2. `bfsProgram` and `bfsLean` agree (computational equivalence). -/

variable {V : Type} [DecidableEq V]

/-- Pure-Lean BFS reference. Returns an association list from every
    reachable vertex to its shortest-path distance from `s`. -/
def bfsLean (ctx : Context V) (s : V) : List (V × Nat) :=
  let rec go (fuel : Nat) (queue : List (V × Nat)) (dist : List (V × Nat)) :
      List (V × Nat) :=
    match fuel with
    | 0 => dist
    | fuel + 1 =>
      match queue with
      | [] => dist
      | (u, d) :: rest =>
        let ns := ctx.vertices.filter (fun w => ctx.isAdj u w)
        let unvisited := ns.filter (fun n => (dist.lookup n).isNone)
        let newPairs := unvisited.map (fun n => (n, d + 1))
        go fuel (rest ++ newPairs) (newPairs ++ dist)
  -- Bound by `|V|² + 1`, which is a safe upper bound on BFS work.
  let bound := ctx.vertices.length * ctx.vertices.length + 1
  go bound [(s, 0)] [(s, 0)]

/-! ## Correctness scaffold

Two correctness statements, in increasing strength:

1. **Soundness**: if `(v, d) ∈ bfsLean ctx s`, then there is a walk of
   length `d` from `s` to `v`.
2. **Optimality**: that `d` is the *shortest* such length.

We state both and leave the proofs as `sorry` — the headline
deliverable of this file is "BFS in GraphIR runs and produces the right
output on examples"; the full correctness proof is the next milestone.
-/

/-- Reachability via a `Toy.Walk`. -/
def Reachable (G : Toy.Graph V) (s v : V) : Prop :=
  ∃ (w : Toy.Walk G s v), True

/-- "There is a walk of length exactly `d` from `s` to `v`". -/
def WalkOfLength (G : Toy.Graph V) (s v : V) (d : Nat) : Prop :=
  ∃ (w : Toy.Walk G s v), w.length = d

/-- Append an edge to the end of a walk. -/
def walkAppendEdge {G : Toy.Graph V} : ∀ {u v w : V}, Toy.Walk G u v → G.edge v w → Toy.Walk G u w
  | _, _, _, .nil, h => .cons h .nil
  | _, _, _, .cons h p, h' => .cons h (walkAppendEdge p h')

omit [DecidableEq V] in
theorem walkAppendEdge_length {G : Toy.Graph V} :
    ∀ {u v w : V} (p : Toy.Walk G u v) (h : G.edge v w),
    (walkAppendEdge p h).length = p.length + 1
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons _ p, h' => by
    simp only [walkAppendEdge, Toy.Walk.length_cons, walkAppendEdge_length p h']

/-- **Soundness — helper.** The `go` loop preserves the invariant that
    every `(u, e)` in `queue` or `dist` corresponds to a walk of length
    `e` from `s` to `u`. -/
private lemma bfsLean_go_sound (G : Toy.Graph V) (ctx : Context V)
    (h_adj : ∀ u w, ctx.isAdj u w = true ↔ G.edge u w)
    (s : V) :
    ∀ (fuel : Nat) (queue dist : List (V × Nat)),
      (∀ p ∈ queue, WalkOfLength G s p.1 p.2) →
      (∀ p ∈ dist, WalkOfLength G s p.1 p.2) →
      ∀ p ∈ bfsLean.go ctx fuel queue dist, WalkOfLength G s p.1 p.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intros queue dist _ hDist p hp
    have : bfsLean.go ctx 0 queue dist = dist := rfl
    rw [this] at hp
    exact hDist p hp
  | succ fuel ih =>
    intros queue dist hQueue hDist p hp
    cases queue with
    | nil =>
      have hEq : bfsLean.go ctx (fuel + 1) [] dist = dist := rfl
      rw [hEq] at hp
      exact hDist p hp
    | cons head rest =>
      obtain ⟨u, d⟩ := head
      have hEq : bfsLean.go ctx (fuel + 1) ((u, d) :: rest) dist =
          bfsLean.go ctx fuel
            (rest ++ ((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
              (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1)))
            ((((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
              (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1))) ++ dist) := rfl
      rw [hEq] at hp
      have hWalkU : WalkOfLength G s u d := hQueue (u, d) (List.mem_cons_self)
      have hNewPairs : ∀ q ∈ ((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
            (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1)),
            WalkOfLength G s q.1 q.2 := by
        intro q hq
        simp only [List.mem_map, List.mem_filter] at hq
        obtain ⟨n, ⟨⟨_, hAdj⟩, _⟩, rfl⟩ := hq
        have hEdge : G.edge u n := (h_adj u n).mp hAdj
        obtain ⟨w, hLen⟩ := hWalkU
        exact ⟨walkAppendEdge w hEdge, by rw [walkAppendEdge_length, hLen]⟩
      apply ih
      · intro q hq
        rcases List.mem_append.mp hq with hRest | hNew
        · exact hQueue q (List.mem_cons_of_mem _ hRest)
        · exact hNewPairs q hNew
      · intro q hq
        rcases List.mem_append.mp hq with hNew | hOld
        · exact hNewPairs q hNew
        · exact hDist q hOld
      · exact hp

/-- **Soundness.** Every `(v, d)` returned by `bfsLean` corresponds to
    an actual walk of length `d` in `G`. Bridge between context and
    graph: `ctx.isAdj u w = true ↔ G.edge u w`. -/
theorem bfsLean_sound (G : Toy.Graph V) (ctx : Context V)
    (h_adj : ∀ u w, ctx.isAdj u w = true ↔ G.edge u w)
    (s v : V) (d : Nat) :
    (v, d) ∈ bfsLean ctx s → WalkOfLength G s v d := by
  intro hMem
  unfold bfsLean at hMem
  apply bfsLean_go_sound G ctx h_adj s _ _ _ _ _ (v, d) hMem
  · intro p hp
    -- queue = [(s, 0)], so p = (s, 0).
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨Toy.Walk.nil, rfl⟩
  · intro p hp
    -- dist = [(s, 0)], same as queue.
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨Toy.Walk.nil, rfl⟩

/-! ### Helpers for BFS optimality -/

/-- The `go` loop preserves nodup-of-keys on `dist`. Each iteration only
    adds `(v, d+1)` for `v` that are NOT already in `dist` (via the
    `unvisited` filter), and the new vertices themselves are distinct
    (assuming `ctx.vertices.Nodup`). -/
private lemma bfsLean_go_dist_keys_nodup (ctx : Context V)
    (h_ctx_nodup : ctx.vertices.Nodup) :
    ∀ (fuel : Nat) (queue dist : List (V × Nat)),
      (dist.map Prod.fst).Nodup →
      ((bfsLean.go ctx fuel queue dist).map Prod.fst).Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intros queue dist hDist
    exact hDist
  | succ fuel ih =>
    intros queue dist hDist
    cases queue with
    | nil => exact hDist
    | cons head rest =>
      obtain ⟨u, d⟩ := head
      have hEq : bfsLean.go ctx (fuel + 1) ((u, d) :: rest) dist =
          bfsLean.go ctx fuel
            (rest ++ ((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
              (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1)))
            ((((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
              (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1))) ++ dist) := rfl
      rw [hEq]
      apply ih
      -- Need: (newPairs ++ dist).map fst has Nodup.
      set ns := ctx.vertices.filter (fun w => ctx.isAdj u w) with hns_def
      set unvisited := ns.filter (fun n => (dist.lookup n).isNone) with hunvis_def
      set newPairs := unvisited.map (fun n => (n, d + 1)) with hnp_def
      -- newPairs.map fst = unvisited (since map (·,d+1) then fst = identity).
      have h_np_fst : newPairs.map Prod.fst = unvisited := by
        rw [hnp_def, List.map_map]
        exact List.map_id _
      -- (newPairs ++ dist).map fst = unvisited ++ dist.map fst.
      rw [List.map_append, h_np_fst]
      -- Show: (unvisited ++ dist.map fst).Nodup.
      -- 1. unvisited.Nodup: filter preserves Nodup; ns.Nodup from filter of ctx.vertices.Nodup.
      have h_ns_nodup : ns.Nodup := h_ctx_nodup.filter _
      have h_unvis_nodup : unvisited.Nodup := h_ns_nodup.filter _
      -- 2. dist.map fst is Nodup (by hDist).
      -- 3. Disjoint: every n in unvisited has (dist.lookup n).isNone = true,
      --    so n ∉ dist's keys.
      have h_disj : ∀ x, x ∈ unvisited → x ∉ dist.map Prod.fst := by
        intro x hx
        simp [hunvis_def, hns_def, List.mem_filter] at hx
        intro hxKeys
        rcases List.mem_map.mp hxKeys with ⟨⟨x', d'⟩, hmem, hx_eq⟩
        simp at hx_eq
        subst hx_eq
        exact hx.2.1 x' d' hmem rfl
      exact List.Nodup.append h_unvis_nodup hDist h_disj

/-- The initial dist `[(s, 0)]` is contained in the final BFS result. The
    `go` loop never removes entries from `dist`. -/
private lemma bfsLean_go_dist_subset (ctx : Context V) :
    ∀ (fuel : Nat) (queue dist : List (V × Nat)) (p : V × Nat),
      p ∈ dist → p ∈ bfsLean.go ctx fuel queue dist := by
  intro fuel
  induction fuel with
  | zero =>
    intros queue dist p hp
    exact hp
  | succ fuel ih =>
    intros queue dist p hp
    cases queue with
    | nil => exact hp
    | cons head rest =>
      obtain ⟨u, d⟩ := head
      have hEq : bfsLean.go ctx (fuel + 1) ((u, d) :: rest) dist =
          bfsLean.go ctx fuel
            (rest ++ ((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
              (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1)))
            ((((ctx.vertices.filter (fun w => ctx.isAdj u w)).filter
              (fun n => (dist.lookup n).isNone)).map (fun n => (n, d + 1))) ++ dist) := rfl
      rw [hEq]
      apply ih
      exact List.mem_append_right _ hp

/-- The initial entry `(s, 0)` is always in the final BFS result. -/
private lemma bfsLean_start_in_result (ctx : Context V) (s : V) :
    (s, 0) ∈ bfsLean ctx s := by
  unfold bfsLean
  exact bfsLean_go_dist_subset ctx _ _ _ (s, 0) (by simp)

/-- *Uniqueness of distance per vertex.* If a vertex `v` appears twice
    in `bfsLean ctx s`, the two distances must agree. -/
private lemma bfsLean_dist_unique (ctx : Context V) (h_ctx_nodup : ctx.vertices.Nodup)
    (s : V) {v : V} {d1 d2 : Nat}
    (h1 : (v, d1) ∈ bfsLean ctx s) (h2 : (v, d2) ∈ bfsLean ctx s) :
    d1 = d2 := by
  have hNodup : ((bfsLean ctx s).map Prod.fst).Nodup := by
    unfold bfsLean
    exact bfsLean_go_dist_keys_nodup ctx h_ctx_nodup _ _ _ (by simp)
  -- Extract from list nodup of map keys.
  by_contra hne
  obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem h1
  obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem h2
  -- (l.map fst)[i] = v = (l.map fst)[j]; by nodup of map, i = j.
  have h_map_i : ((bfsLean ctx s).map Prod.fst)[i]'
      (by rw [List.length_map]; exact hi_lt) = v := by
    rw [List.getElem_map]; rw [hi_eq]
  have h_map_j : ((bfsLean ctx s).map Prod.fst)[j]'
      (by rw [List.length_map]; exact hj_lt) = v := by
    rw [List.getElem_map]; rw [hj_eq]
  have h_ij : i = j := by
    have h_inj := List.Nodup.getElem_inj_iff hNodup
        (i := i) (j := j)
        (hi := by rw [List.length_map]; exact hi_lt)
        (hj := by rw [List.length_map]; exact hj_lt)
    exact h_inj.mp (h_map_i.trans h_map_j.symm)
  subst h_ij
  rw [hi_eq] at hj_eq
  injection hj_eq with _ h_d
  exact hne h_d

/-- **Optimality.** The distance `d` returned by `bfsLean` is the
    *shortest* walk length from `s` to `v`: any other walk is at least
    as long.

    The full proof requires a BFS-layer invariant: every vertex
    reachable in `≤ d'` steps enters `dist` with distance `≤ d'`. This
    uses the helpers `bfsLean_go_dist_keys_nodup`, `bfsLean_go_dist_subset`,
    `bfsLean_dist_unique`, and `bfsLean_start_in_result`. The remaining
    obstacle is the *completeness* claim: BFS visits all reachable
    vertices within its fuel budget (`|V|² + 1`), which requires a
    potential-function argument or FIFO queue invariant. We close the
    `v = s` subcase (using uniqueness + initial entry) and leave the
    general case as `sorry`. -/
theorem bfsLean_optimal (G : Toy.Graph V) (ctx : Context V)
    (h_adj : ∀ u w, ctx.isAdj u w = true ↔ G.edge u w)
    (h_ctx_nodup : ctx.vertices.Nodup)
    (s v : V) (d : Nat) :
    (v, d) ∈ bfsLean ctx s →
    ∀ d' (_ : WalkOfLength G s v d'), d ≤ d' := by
  intro h_in d' h_walk
  -- Subcase v = s: by uniqueness, d = 0; then d ≤ d' holds for any d'.
  by_cases h_v_eq_s : v = s
  · rw [h_v_eq_s] at h_in
    have h_d_eq : d = 0 := bfsLean_dist_unique ctx h_ctx_nodup s h_in
                              (bfsLean_start_in_result ctx s)
    omega
  · -- v ≠ s. Subcase d' = 0 is impossible (walk of length 0 ⇒ v = s).
    by_cases h_d'_zero : d' = 0
    · exfalso
      subst h_d'_zero
      obtain ⟨w, hLen⟩ := h_walk
      cases w with
      | nil => exact h_v_eq_s rfl
      | cons _ _ => simp [Toy.Walk.length] at hLen
    · -- v ≠ s and d' ≥ 1: needs the full BFS-layer argument.
      sorry

end Hackathon.GraphIR.BFS
