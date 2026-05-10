import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Walk

/-
# Matching, alternating walks, augmenting paths

We use Mathlib's `SimpleGraph.Subgraph.IsMatching` as the definition
of a matching: a subgraph in which every vertex has at most one
incident edge.

On top of this we define:

* `IsAlternating M w` — the walk `w` alternates between edges of `M`
  and edges of `G \ M`.
* `IsAugmenting M w` — `w` is an alternating path whose endpoints are
  both unmatched in `M`. (An "M-augmenting path".)

These are the central definitions for Berge's theorem and for
proving correctness of matching algorithms (Phase 2 of the plan).
-/

namespace Hackathon

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/- ## Matching basics -/

/--
A *matching* in `G`: an edge subgraph `M ≤ G.spanningCoe` (i.e. a
subgraph with `M.verts = univ`) whose edges form a matching.
For convenience we work directly with `M : G.Subgraph` and require
`M.IsMatching` (and possibly that `M.verts = Set.univ` for "spanning").

Mathlib reference: `SimpleGraph.Subgraph.IsMatching`.
-/
abbrev Matching (G : SimpleGraph V) := { M : G.Subgraph // M.IsMatching }

/--
A vertex `v` is *unmatched* (free, exposed) in matching `M` if it is
not in `M.verts`. (For an `IsMatching` subgraph, this is equivalent
to "no edge of `M` is incident to `v`".)
-/
def IsUnmatched (M : G.Subgraph) (v : V) : Prop := v ∉ M.verts

/- ## Alternating walks -/

/--
A walk `w` in `G` is *M-alternating* if consecutive edges alternate
between edges of `M` and edges not in `M`. We state this on the
edge sequence `w.edges`.

Equivalent formulation: for every two consecutive edges `e₁, e₂` in
the walk, exactly one of them lies in `M.edgeSet`.
-/
def IsAlternating (M : G.Subgraph) {u v : V} (w : G.Walk u v) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i + 1 < w.edges.length),
    (w.edges[i]'(Nat.lt_of_succ_lt hi) ∈ M.edgeSet) ≠
    (w.edges[i + 1]'hi ∈ M.edgeSet)

/- ## Augmenting paths -/

/--
A walk `w` from `u` to `v` is `M`-*augmenting* iff:
1. it is a path (no repeated vertices),
2. it is `M`-alternating,
3. its first edge is *not* in `M`,
4. its last edge is *not* in `M` (equivalently, both endpoints are
   unmatched).

The first/last conditions force the walk's edge sequence to be of the
form  `e₀ ∉ M, e₁ ∈ M, e₂ ∉ M, …, eₖ ∉ M`, with `k` even, so the path
has odd length and "augmenting via symmetric difference" gives a
matching one larger than `M`.
-/
structure IsAugmenting (M : G.Subgraph) {u v : V} (w : G.Walk u v) : Prop where
  nonEmpty       : 1 ≤ w.length
  isPath         : w.IsPath
  alternating    : IsAlternating M w
  startUnmatched : IsUnmatched M u
  endUnmatched   : IsUnmatched M v

/- ## Practice lemmas -/

/-- ★  The empty subgraph is a matching. -/
example : (⊥ : G.Subgraph).IsMatching := by
  intro v hv
  exact hv.elim

/-- ★★  In a matching, adjacency is a *partial function*: each vertex has at
most one match. -/
example {M : G.Subgraph} (hM : M.IsMatching) {u v w : V}
    (huv : M.Adj u v) (huw : M.Adj u w) : v = w := by
  obtain ⟨x, _, hux⟩ := hM (M.edge_vert huv)
  exact (hux v huv).trans (hux w huw).symm

/-- ★★  The empty walk is alternating in any matching `M` (vacuously). -/
example (M : G.Subgraph) (v : V) :
    IsAlternating M (Walk.nil : G.Walk v v) := by
  intro i hi
  simp [Walk.edges] at hi

/-- ★★★  Every non-empty `M`-augmenting path has odd length.
The empty case (`u = v`, `w = .nil`) is excluded by `1 ≤ w.length`. -/
example {M : G.Subgraph} {u v : V} (w : G.Walk u v) (h : IsAugmenting M w)
    (hlen : 1 ≤ w.length) :
    Odd w.length := by
  classical
  obtain ⟨_, _, hAlt, hu, hv⟩ := h
  have hLE : w.edges.length = w.length := w.length_edges
  have hpos : 0 < w.edges.length := by rw [hLE]; exact hlen
  have hEdgesNonempty : w.edges ≠ [] := List.length_pos_iff.mp hpos
  -- Step 1: First edge of `w` is not in `M.edgeSet`. Cases on `w`.
  have h_first : (w.edges[0]'hpos) ∉ M.edgeSet := by
    cases w with
    | nil => exact absurd hpos (by simp [Walk.edges])
    | @cons a b c hadj p =>
    simp only [Walk.edges_cons, List.getElem_cons_zero]
    intro hMem
    have hVert : a ∈ M.verts := M.edge_vert (Subgraph.mem_edgeSet.mp hMem)
    exact hu hVert
  -- Step 2: Last edge of `w` contains `v`, so isn't in `M.edgeSet`.
  have hLastEdge : w.edges.getLast hEdgesNonempty = s(w.penultimate, v) :=
    Walk.getLast_edges_eq_mk_penultimate_end _
  have h_last : (w.edges[w.edges.length - 1]'(by omega)) ∉ M.edgeSet := by
    have hEq : w.edges[w.edges.length - 1]'(by omega) = w.edges.getLast hEdgesNonempty := by
      rw [List.getLast_eq_getElem]
    rw [hEq, hLastEdge]
    intro hMem
    apply hv
    exact M.mem_verts_of_mem_edge hMem (by simp [Sym2.mem_iff])
  -- Step 3: Prove by induction on `i` that `(w.edges[i] ∈ M.edgeSet) ↔ Odd i`.
  have hKey : ∀ i (hi : i < w.edges.length),
      (w.edges[i] ∈ M.edgeSet ↔ Odd i) := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨fun hMem => absurd hMem h_first, fun hOdd => ?_⟩
      exact absurd hOdd (by decide)
    | succ k ih =>
      have hk : k < w.edges.length := Nat.lt_of_succ_lt hi
      have ihk := ih hk
      have hAltLocal : (w.edges[k]'hk ∈ M.edgeSet) ≠ (w.edges[k+1]'hi ∈ M.edgeSet) :=
        hAlt hi
      constructor
      · intro hSucc
        have h_k_notIn : w.edges[k]'hk ∉ M.edgeSet := fun hKin =>
          hAltLocal (propext (Iff.intro (fun _ => hSucc) (fun _ => hKin)))
        have hNotOddK : ¬ Odd k := fun hOdd => h_k_notIn (ihk.mpr hOdd)
        rcases Nat.even_or_odd k with hEvenK | hOddK
        · exact hEvenK.add_one
        · exact absurd hOddK hNotOddK
      · intro hOddSucc
        rcases hOddSucc with ⟨j, hj⟩
        have hEvenK : Even k := ⟨j, by omega⟩
        have hNotOddK : ¬ Odd k := fun hOdd => (Nat.not_odd_iff_even.mpr hEvenK) hOdd
        have h_k_notIn : w.edges[k]'hk ∉ M.edgeSet := fun hMem => hNotOddK (ihk.mp hMem)
        by_contra hSuccNotIn
        apply hAltLocal
        exact propext (Iff.intro (fun hKin => absurd hKin h_k_notIn)
                                  (fun hSuccIn => absurd hSuccIn hSuccNotIn))
  -- Step 4: At index `length - 1`, edge is not in M, so `length - 1` is even, so `length` is odd.
  have hLastIff := hKey (w.edges.length - 1) (by omega)
  have hNotOddLast : ¬ Odd (w.edges.length - 1) := fun hO => h_last (hLastIff.mpr hO)
  rcases Nat.even_or_odd (w.edges.length - 1) with hE | hO
  · rw [← hLE]
    rcases hE with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · exact absurd hO hNotOddLast

end Hackathon
