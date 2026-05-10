import Hackathon.Graph.Matching

/-
# Rung 1 — The augmentation lemma

If `P` is an `M`-augmenting path, then the *symmetric difference*
`M △ edges(P)` is again a matching, and its size is `|M| + 1`.

This is the engine of every matching algorithm: each augmenting path
strictly increases the matching size by 1, so we can only find at most
|V|/2 of them.

## Sub-lemmas

* `xor_subgraph M w` — the symmetric difference of `M.edgeSet` and
  the edges of `w`, viewed as a subgraph.
* Adjacency in the xor: `(M △ w).Adj a b ↔ (M.Adj a b ↔ s(a,b) ∉ w.edges)`.
* The xor is a matching when `w` is `M`-augmenting: every vertex has
  at most one incident edge.
* The xor has `|M| + 1` edges (one fewer `M`-edge, two more new edges,
  net +1, because the path has even number of `M`-edges interspersed
  with one more non-`M`-edge).

We leave statements with `sorry` for now. Filling these in is **Phase 2,
Rung 1** of the plan.
-/

namespace Hackathon

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/--
The symmetric difference of a matching `M` with the edges of a walk `w`,
returned as a subgraph of `G`. Adjacency:

  `Adj a b` iff exactly one of `M.Adj a b` and `s(a,b) ∈ w.edges` holds
  (and `G.Adj a b`, to remain a subgraph of `G`).

The vertex set is `M.verts ∪ w.support` (the matched vertices of M plus
the vertices visited by the walk). This is the set of vertices that
could be incident to an `xorWith` edge.
-/
def xorWith (M : G.Subgraph) {u v : V} (w : G.Walk u v) : G.Subgraph where
  verts := M.verts ∪ {x | x ∈ w.support}
  Adj a b := G.Adj a b ∧ (M.Adj a b ↔ s(a, b) ∉ w.edges)
  adj_sub h := h.1
  edge_vert := by
    intro a b ⟨_, hxor⟩
    by_cases hM : M.Adj a b
    · left; exact M.edge_vert hM
    · right
      have hSin : s(a, b) ∈ w.edges := by
        by_contra h
        exact hM (hxor.mpr h)
      exact Walk.fst_mem_support_of_mem_edges _ hSin
  symm := by
    intro a b ⟨hab, hxor⟩
    refine ⟨hab.symm, ?_⟩
    rw [show s(b, a) = s(a, b) from Sym2.eq_swap]
    constructor
    · intro h
      exact hxor.mp (M.symm h)
    · intro h
      exact M.symm (hxor.mpr h)

/-! ### Helpers for the augmentation lemma -/

/-- For `x` not in walk's support, no walk-edge is incident to `x`. -/
private lemma not_mem_support_implies_no_walk_edge
    {u v : V} {w : G.Walk u v} {x : V} (hx : x ∉ w.support) (y : V) :
    s(x, y) ∉ w.edges := by
  intro h
  exact hx (w.fst_mem_support_of_mem_edges h)

/-- Helper: in an `M`-augmenting path `w`, every interior support vertex
    (not the start `u` or end `v`) is matched in `M`. -/
private lemma IsAugmenting.interior_in_M_verts
    {M : G.Subgraph} {u v : V} {w : G.Walk u v} (hw : IsAugmenting M w)
    {x : V} (hx : x ∈ w.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    x ∈ M.verts := by
  -- Find x's position in support.
  obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hx
  have hLen_supp : w.support.length = w.length + 1 := w.length_support
  rw [hLen_supp] at hk_lt
  -- Derive 0 < k < w.length.
  have hk_ne_0 : k ≠ 0 := fun h => by
    subst h
    have h1 : w.support[0] = x := hk_eq
    rw [w.support_getElem_zero] at h1
    exact hxu h1.symm
  have hk_ne_len : k ≠ w.length := fun h => by
    subst h
    have h1 : w.support[w.length] = x := hk_eq
    rw [w.support_getElem_length] at h1
    exact hxv h1.symm
  have hk_lt_len : k < w.length := lt_of_le_of_ne (Nat.lt_succ_iff.mp hk_lt) hk_ne_len
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_0
  -- Replace k = km1 + 1 to avoid the (k-1)+1 vs k dependent-rewrite issue.
  obtain ⟨km1, rfl⟩ : ∃ km1, k = km1 + 1 := ⟨k - 1, by omega⟩
  -- Now hypotheses use km1 + 1.
  have h_edges_len : w.edges.length = w.length := w.length_edges
  have h_km1_succ_lt_edges : km1 + 1 < w.edges.length := by rw [h_edges_len]; exact hk_lt_len
  have h_km1_lt_edges : km1 < w.edges.length := by omega
  -- Apply alternating at i := km1 (gives edges[km1] ≠ edges[km1+1] cleanly).
  have h_alt := hw.alternating (i := km1) h_km1_succ_lt_edges
  -- Dart accessors.
  have h_dart_succ_lt : km1 + 1 < w.darts.length := by rw [w.length_darts]; exact hk_lt_len
  have h_dart_lt : km1 < w.darts.length := by omega
  -- (w.darts[km1+1]).fst = w.support.dropLast[km1+1] = w.support[km1+1] = x.
  have h_drop_succ_lt : km1 + 1 < w.support.dropLast.length := by
    rw [List.length_dropLast, hLen_supp]; omega
  have h_dart_succ_fst : (w.darts[km1 + 1]'h_dart_succ_lt).fst = x := by
    rw [w.fst_darts_getElem h_dart_succ_lt]
    rw [List.getElem_dropLast]
    exact hk_eq
  -- (w.darts[km1]).snd = w.support.tail[km1] = w.support[km1+1] = x.
  have h_tail_lt : km1 < w.support.tail.length := by
    rw [List.length_tail, hLen_supp]; omega
  have h_dart_snd : (w.darts[km1]'h_dart_lt).snd = x := by
    rw [w.snd_darts_getElem h_dart_lt]
    have h_tail_eq : w.support.tail[km1]'h_tail_lt =
                     w.support[km1 + 1]'(by rw [hLen_supp]; omega) := by
      rw [List.getElem_tail]
    rw [h_tail_eq]
    exact hk_eq
  -- w.edges[km1] = s(?, x), w.edges[km1+1] = s(x, ?).
  have h_edge_km1_eq : w.edges[km1]'h_km1_lt_edges =
                       s((w.darts[km1]'h_dart_lt).fst, x) := by
    show (w.darts.map SimpleGraph.Dart.edge)[km1]'_ = _
    rw [List.getElem_map]
    show SimpleGraph.Dart.edge _ = _
    unfold SimpleGraph.Dart.edge
    rw [h_dart_snd]
  have h_edge_succ_eq : w.edges[km1 + 1]'h_km1_succ_lt_edges =
                        s(x, (w.darts[km1 + 1]'h_dart_succ_lt).snd) := by
    show (w.darts.map SimpleGraph.Dart.edge)[km1 + 1]'_ = _
    rw [List.getElem_map]
    show SimpleGraph.Dart.edge _ = _
    unfold SimpleGraph.Dart.edge
    rw [h_dart_succ_fst]
  -- Case split on which edge is in M.
  classical
  by_cases h_M_km1 : w.edges[km1]'h_km1_lt_edges ∈ M.edgeSet
  · -- M-edge at km1 has x as second component.
    rw [h_edge_km1_eq] at h_M_km1
    have : M.Adj (w.darts[km1]'h_dart_lt).fst x := Subgraph.mem_edgeSet.mp h_M_km1
    exact M.edge_vert this.symm
  · -- M-edge at km1+1 by alternation.
    have h_M_succ : w.edges[km1 + 1]'h_km1_succ_lt_edges ∈ M.edgeSet := by
      by_contra h
      apply h_alt
      exact propext (Iff.intro (fun hT => absurd hT h_M_km1) (fun hT => absurd hT h))
    rw [h_edge_succ_eq] at h_M_succ
    have : M.Adj x (w.darts[km1 + 1]'h_dart_succ_lt).snd := Subgraph.mem_edgeSet.mp h_M_succ
    exact M.edge_vert this


/-- Stronger helper: in an `M`-augmenting path, for an interior support vertex
    `a`, `a`'s M-partner is one of its two walk-neighbors. Concretely, if `a`
    is at support position `km1+1` with `0 < km1+1 < w.length`, then `a`'s
    M-partner equals either `(w.darts[km1]).fst` (predecessor) or
    `(w.darts[km1+1]).snd` (successor).
    Combined with the fact that `s(a, M_partner) ∈ w.edges`, this gives the
    structural data needed to construct xor-partners. -/
private lemma IsAugmenting.M_partner_is_walk_neighbor
    {M : G.Subgraph} {u v : V} {w : G.Walk u v} (hw : IsAugmenting M w)
    (hM : M.IsMatching) {a : V} (ha_support : a ∈ w.support)
    (ha_ne_u : a ≠ u) (ha_ne_v : a ≠ v)
    {b : V} (hM_ab : M.Adj a b) :
    s(a, b) ∈ w.edges := by
  -- The proof: a is interior, two walk-edges; by alternation, one ∈ M; by
  -- M-uniqueness, that M-walk-edge has b as the other endpoint.
  -- Essentially same reasoning as interior_in_M_verts, but extracting more info.
  obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem ha_support
  have hLen_supp : w.support.length = w.length + 1 := w.length_support
  rw [hLen_supp] at hk_lt
  have hk_ne_0 : k ≠ 0 := fun h => by
    subst h
    have h1 : w.support[0] = a := hk_eq
    rw [w.support_getElem_zero] at h1
    exact ha_ne_u h1.symm
  have hk_ne_len : k ≠ w.length := fun h => by
    subst h
    have h1 : w.support[w.length] = a := hk_eq
    rw [w.support_getElem_length] at h1
    exact ha_ne_v h1.symm
  have hk_lt_len : k < w.length := lt_of_le_of_ne (Nat.lt_succ_iff.mp hk_lt) hk_ne_len
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_0
  obtain ⟨km1, rfl⟩ : ∃ km1, k = km1 + 1 := ⟨k - 1, by omega⟩
  have h_edges_len : w.edges.length = w.length := w.length_edges
  have h_km1_succ_lt_edges : km1 + 1 < w.edges.length := by rw [h_edges_len]; exact hk_lt_len
  have h_km1_lt_edges : km1 < w.edges.length := by omega
  have h_dart_succ_lt : km1 + 1 < w.darts.length := by rw [w.length_darts]; exact hk_lt_len
  have h_dart_lt : km1 < w.darts.length := by omega
  have h_dart_snd : (w.darts[km1]'h_dart_lt).snd = a := by
    rw [w.snd_darts_getElem h_dart_lt]
    rw [List.getElem_tail]
    exact hk_eq
  have h_dart_succ_fst : (w.darts[km1 + 1]'h_dart_succ_lt).fst = a := by
    rw [w.fst_darts_getElem h_dart_succ_lt]
    rw [List.getElem_dropLast]
    exact hk_eq
  have h_edge_km1_eq : w.edges[km1]'h_km1_lt_edges =
                       s((w.darts[km1]'h_dart_lt).fst, a) := by
    show (w.darts.map SimpleGraph.Dart.edge)[km1]'_ = _
    rw [List.getElem_map]
    show SimpleGraph.Dart.edge _ = _
    unfold SimpleGraph.Dart.edge
    rw [h_dart_snd]
  have h_edge_succ_eq : w.edges[km1 + 1]'h_km1_succ_lt_edges =
                        s(a, (w.darts[km1 + 1]'h_dart_succ_lt).snd) := by
    show (w.darts.map SimpleGraph.Dart.edge)[km1 + 1]'_ = _
    rw [List.getElem_map]
    show SimpleGraph.Dart.edge _ = _
    unfold SimpleGraph.Dart.edge
    rw [h_dart_succ_fst]
  have h_alt := hw.alternating (i := km1) h_km1_succ_lt_edges
  classical
  -- Which walk-edge is in M? By alternation, one is. By M-uniqueness, b is the other vertex.
  by_cases h_M_km1 : w.edges[km1]'h_km1_lt_edges ∈ M.edgeSet
  · -- s(b_pred, a) ∈ M. M's partner of a is b_pred. So b = b_pred.
    rw [h_edge_km1_eq] at h_M_km1
    have h_M_adj : M.Adj (w.darts[km1]'h_dart_lt).fst a := Subgraph.mem_edgeSet.mp h_M_km1
    have h_b_eq : b = (w.darts[km1]'h_dart_lt).fst := by
      obtain ⟨b', hM_b', hUniq⟩ := hM (M.edge_vert hM_ab)
      have h1 : b = b' := hUniq b hM_ab
      have h2 : (w.darts[km1]'h_dart_lt).fst = b' := hUniq _ h_M_adj.symm
      rw [h1, h2]
    rw [h_b_eq]
    -- s(a, b_pred) = s(b_pred, a) ∈ w.edges (via h_edge_km1_eq).
    rw [show s(a, (w.darts[km1]'h_dart_lt).fst) = s((w.darts[km1]'h_dart_lt).fst, a)
            from Sym2.eq_swap]
    rw [← h_edge_km1_eq]
    exact List.getElem_mem _
  · -- w.edges[km1+1] ∈ M (alternation). M's partner is b_succ.
    have h_M_succ : w.edges[km1 + 1]'h_km1_succ_lt_edges ∈ M.edgeSet := by
      by_contra h
      apply h_alt
      exact propext (Iff.intro (fun hT => absurd hT h_M_km1) (fun hT => absurd hT h))
    rw [h_edge_succ_eq] at h_M_succ
    have h_M_adj : M.Adj a (w.darts[km1 + 1]'h_dart_succ_lt).snd := Subgraph.mem_edgeSet.mp h_M_succ
    have h_b_eq : b = (w.darts[km1 + 1]'h_dart_succ_lt).snd := by
      obtain ⟨b', hM_b', hUniq⟩ := hM (M.edge_vert hM_ab)
      have h1 : b = b' := hUniq b hM_ab
      have h2 : (w.darts[km1 + 1]'h_dart_succ_lt).snd = b' := hUniq _ h_M_adj
      rw [h1, h2]
    rw [h_b_eq, ← h_edge_succ_eq]
    exact List.getElem_mem _

/-- For a walk-edge at position `i`, the edge is `s(support[i], support[i+1])`. -/
private lemma walk_edge_eq_support {u v : V} (w : G.Walk u v) (i : ℕ)
    (hi : i < w.edges.length) :
    w.edges[i]'hi = s(w.support[i]'(by rw [w.length_support]; rw [w.length_edges] at hi; omega),
                     w.support[i + 1]'(by rw [w.length_support]; rw [w.length_edges] at hi; omega)) := by
  have h_dart_lt : i < w.darts.length := by rw [w.length_darts]; rw [w.length_edges] at hi; exact hi
  show (w.darts.map SimpleGraph.Dart.edge)[i]'_ = _
  rw [List.getElem_map]
  show SimpleGraph.Dart.edge _ = _
  unfold SimpleGraph.Dart.edge
  congr 1
  · rw [w.fst_darts_getElem h_dart_lt, List.getElem_dropLast]
  · rw [w.snd_darts_getElem h_dart_lt, List.getElem_tail]

/--
**Augmentation lemma.** If `w` is `M`-augmenting, then `xorWith M w`
is a matching. -/
theorem IsAugmenting.xorWith_isMatching
    {M : G.Subgraph} (hM : M.IsMatching) {u v : V}
    {w : G.Walk u v} (hw : IsAugmenting M w) :
    (xorWith M w).IsMatching := by
  classical
  intro a ha
  have h_edges_len : w.edges.length = w.length := w.length_edges
  have hLen_supp : w.support.length = w.length + 1 := w.length_support
  have hNodup : w.support.Nodup := hw.isPath.support_nodup
  by_cases hMv : a ∈ M.verts
  · -- Case A: a ∈ M.verts. Get M-partner b_star.
    obtain ⟨b_star, hM_b_star, hM_unique⟩ := hM hMv
    have ha_ne_u : a ≠ u := fun heq => hw.startUnmatched (heq ▸ hMv)
    have ha_ne_v : a ≠ v := fun heq => hw.endUnmatched (heq ▸ hMv)
    by_cases h_walk_M : s(a, b_star) ∈ w.edges
    · -- A.2: M-edge on walk. a interior. xor-partner = other walk-neighbor.
      have h_a_in_support : a ∈ w.support := w.fst_mem_support_of_mem_edges h_walk_M
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem h_a_in_support
      rw [hLen_supp] at hk_lt
      have hk_ne_0 : k ≠ 0 := fun h => by
        subst h
        have h1 : w.support[0] = a := hk_eq
        rw [w.support_getElem_zero] at h1
        exact ha_ne_u h1.symm
      have hk_ne_len : k ≠ w.length := fun h => by
        subst h
        have h1 : w.support[w.length] = a := hk_eq
        rw [w.support_getElem_length] at h1
        exact ha_ne_v h1.symm
      have hk_lt_len : k < w.length := lt_of_le_of_ne (Nat.lt_succ_iff.mp hk_lt) hk_ne_len
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_0
      obtain ⟨km1, rfl⟩ : ∃ km1, k = km1 + 1 := ⟨k - 1, by omega⟩
      have h_km1_succ_lt_e : km1 + 1 < w.edges.length := by rw [h_edges_len]; exact hk_lt_len
      have h_km1_lt_e : km1 < w.edges.length := by omega
      have h_dart_succ_lt : km1 + 1 < w.darts.length := by rw [w.length_darts]; exact hk_lt_len
      have h_dart_lt : km1 < w.darts.length := by omega
      have h_supp_km1_lt : km1 < w.support.length := by rw [hLen_supp]; omega
      have h_supp_km2_lt : km1 + 2 < w.support.length := by rw [hLen_supp]; omega
      have h_dart_snd_eq : (w.darts[km1]'h_dart_lt).snd = a := by
        rw [w.snd_darts_getElem h_dart_lt, List.getElem_tail]; exact hk_eq
      have h_dart_succ_fst_eq : (w.darts[km1 + 1]'h_dart_succ_lt).fst = a := by
        rw [w.fst_darts_getElem h_dart_succ_lt, List.getElem_dropLast]; exact hk_eq
      have h_edge_km1_eq : w.edges[km1]'h_km1_lt_e =
                           s((w.darts[km1]'h_dart_lt).fst, a) := by
        show (w.darts.map SimpleGraph.Dart.edge)[km1]'_ = _
        rw [List.getElem_map]
        show SimpleGraph.Dart.edge _ = _
        unfold SimpleGraph.Dart.edge
        rw [h_dart_snd_eq]
      have h_edge_succ_eq : w.edges[km1 + 1]'h_km1_succ_lt_e =
                            s(a, (w.darts[km1 + 1]'h_dart_succ_lt).snd) := by
        show (w.darts.map SimpleGraph.Dart.edge)[km1 + 1]'_ = _
        rw [List.getElem_map]
        show SimpleGraph.Dart.edge _ = _
        unfold SimpleGraph.Dart.edge
        rw [h_dart_succ_fst_eq]
      have h_alt := hw.alternating (i := km1) h_km1_succ_lt_e
      set bp := (w.darts[km1]'h_dart_lt).fst with hbp_def
      set bs := (w.darts[km1 + 1]'h_dart_succ_lt).snd with hbs_def
      have hbp_val : bp = w.support[km1]'h_supp_km1_lt := by
        show (w.darts[km1]'h_dart_lt).fst = _
        rw [w.fst_darts_getElem h_dart_lt, List.getElem_dropLast]
      have hbs_val : bs = w.support[km1 + 2]'h_supp_km2_lt := by
        show (w.darts[km1 + 1]'h_dart_succ_lt).snd = _
        rw [w.snd_darts_getElem h_dart_succ_lt, List.getElem_tail]
      have h_supp_neq : w.support[km1]'h_supp_km1_lt ≠
                        w.support[km1 + 2]'h_supp_km2_lt := by
        intro h_eq
        have : km1 = km1 + 2 := (List.Nodup.getElem_inj_iff hNodup).mp h_eq
        omega
      have h_bp_neq_bs : bp ≠ bs := fun h => h_supp_neq (hbp_val ▸ hbs_val ▸ h)
      by_cases h_km1_inM : w.edges[km1]'h_km1_lt_e ∈ M.edgeSet
      · -- M-edge at km1. b_star = bp. xor-partner = bs.
        have h_M_bp_a : M.Adj bp a := by
          have : s(bp, a) ∈ M.edgeSet := h_edge_km1_eq ▸ h_km1_inM
          exact Subgraph.mem_edgeSet.mp this
        have h_b_star_eq_bp : b_star = bp := (hM_unique bp h_M_bp_a.symm).symm
        refine ⟨bs, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · have := (w.darts[km1 + 1]'h_dart_succ_lt).adj
            rw [h_dart_succ_fst_eq] at this; exact this
          · constructor
            · intro h_M_a_bs
              exfalso
              have h_bs_eq : bs = b_star := hM_unique bs h_M_a_bs
              exact h_bp_neq_bs (h_b_star_eq_bp.symm.trans h_bs_eq.symm)
            · intro h_notin
              exfalso; apply h_notin
              rw [← h_edge_succ_eq]; exact List.getElem_mem _
        · intro b' h_b'_adj
          obtain ⟨_, h_iff⟩ := h_b'_adj
          by_cases h_M_a_b' : M.Adj a b'
          · exfalso
            have h_b'_eq : b' = b_star := hM_unique b' h_M_a_b'
            have h_b'_eq_bp : b' = bp := h_b'_eq.trans h_b_star_eq_bp
            have h_s_notin : s(a, b') ∉ w.edges := h_iff.mp h_M_a_b'
            apply h_s_notin
            rw [h_b'_eq_bp, show s(a, bp) = s(bp, a) from Sym2.eq_swap, ← h_edge_km1_eq]
            exact List.getElem_mem _
          · have h_s_in : s(a, b') ∈ w.edges := by
              by_contra h; exact h_M_a_b' (h_iff.mpr h)
            rcases List.getElem_of_mem h_s_in with ⟨i, hi_lt, hi_eq⟩
            have h_e_form := walk_edge_eq_support w i hi_lt
            rw [h_e_form] at hi_eq
            rcases Sym2.eq_iff.mp hi_eq.symm with ⟨ha_fst, hb'_snd⟩ | ⟨ha_snd, hb'_fst⟩
            · -- a = support[i]. By Nodup, i = km1 + 1. b' = support[i+1] = bs.
              have h_i_eq : i = km1 + 1 := by
                have h1 : w.support[i]'(by rw [hLen_supp, ← h_edges_len]; omega) =
                          w.support[km1 + 1]'(by rw [hLen_supp]; omega) := by
                  rw [← ha_fst]; exact hk_eq.symm
                exact (List.Nodup.getElem_inj_iff hNodup).mp h1
              subst h_i_eq
              rw [hb'_snd]
              show _ = bs
              symm
              show (w.darts[km1 + 1]'h_dart_succ_lt).snd = _
              rw [w.snd_darts_getElem h_dart_succ_lt, List.getElem_tail]
            · -- a = support[i+1]. i = km1. b' = support[i] = bp. But M.Adj a bp (= h_M_bp_a.symm).
              -- Contradicts ¬M.Adj a b'.
              have h_i_succ : i + 1 = km1 + 1 := by
                have h1 : w.support[i + 1]'(by rw [hLen_supp, ← h_edges_len]; omega) =
                          w.support[km1 + 1]'(by rw [hLen_supp]; omega) := by
                  rw [← ha_snd]; exact hk_eq.symm
                exact (List.Nodup.getElem_inj_iff hNodup).mp h1
              have h_i_eq : i = km1 := by omega
              exfalso
              apply h_M_a_b'
              rw [hb'_fst]
              -- Goal: M.Adj a w.support[i]. Convert to M.Adj a bp via i = km1.
              have h_supp_eq_bp : w.support[i]'(by rw [hLen_supp, ← h_edges_len]; omega) = bp := by
                rw [hbp_val]; congr 1
              rw [h_supp_eq_bp]
              exact h_M_bp_a.symm
      · -- M-edge at km1+1 (by alternation). b_star = bs. xor-partner = bp.
        have h_succ_inM : w.edges[km1 + 1]'h_km1_succ_lt_e ∈ M.edgeSet := by
          by_contra h
          apply h_alt
          exact propext (Iff.intro (fun hT => absurd hT h_km1_inM) (fun hT => absurd hT h))
        have h_M_a_bs : M.Adj a bs := by
          have : s(a, bs) ∈ M.edgeSet := h_edge_succ_eq ▸ h_succ_inM
          exact Subgraph.mem_edgeSet.mp this
        have h_b_star_eq_bs : b_star = bs := (hM_unique bs h_M_a_bs).symm
        refine ⟨bp, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · have := (w.darts[km1]'h_dart_lt).adj
            rw [h_dart_snd_eq] at this; exact this.symm
          · constructor
            · intro h_M_a_bp
              exfalso
              have h_bp_eq : bp = b_star := hM_unique bp h_M_a_bp
              exact h_bp_neq_bs (h_bp_eq.trans h_b_star_eq_bs)
            · intro h_notin
              exfalso; apply h_notin
              rw [show s(a, bp) = s(bp, a) from Sym2.eq_swap, ← h_edge_km1_eq]
              exact List.getElem_mem _
        · intro b' h_b'_adj
          obtain ⟨_, h_iff⟩ := h_b'_adj
          by_cases h_M_a_b' : M.Adj a b'
          · exfalso
            have h_b'_eq : b' = b_star := hM_unique b' h_M_a_b'
            have h_b'_eq_bs : b' = bs := h_b'_eq.trans h_b_star_eq_bs
            have h_s_notin : s(a, b') ∉ w.edges := h_iff.mp h_M_a_b'
            apply h_s_notin
            rw [h_b'_eq_bs, ← h_edge_succ_eq]
            exact List.getElem_mem _
          · have h_s_in : s(a, b') ∈ w.edges := by
              by_contra h; exact h_M_a_b' (h_iff.mpr h)
            rcases List.getElem_of_mem h_s_in with ⟨i, hi_lt, hi_eq⟩
            have h_e_form := walk_edge_eq_support w i hi_lt
            rw [h_e_form] at hi_eq
            rcases Sym2.eq_iff.mp hi_eq.symm with ⟨ha_fst, hb'_snd⟩ | ⟨ha_snd, hb'_fst⟩
            · -- a = support[i]. By Nodup, i = km1 + 1. b' = support[i+1] = bs. But M.Adj a bs.
              have h_i_eq : i = km1 + 1 := by
                have h1 : w.support[i]'(by rw [hLen_supp, ← h_edges_len]; omega) =
                          w.support[km1 + 1]'(by rw [hLen_supp]; omega) := by
                  rw [← ha_fst]; exact hk_eq.symm
                exact (List.Nodup.getElem_inj_iff hNodup).mp h1
              exfalso
              apply h_M_a_b'
              rw [hb'_snd]
              have h_supp_eq_bs :
                  w.support[i + 1]'(by rw [hLen_supp, ← h_edges_len]; omega) = bs := by
                rw [hbs_val]; congr 1; omega
              rw [h_supp_eq_bs]
              exact h_M_a_bs
            · -- a = support[i+1]. i = km1. b' = support[i] = bp.
              have h_i_succ : i + 1 = km1 + 1 := by
                have h1 : w.support[i + 1]'(by rw [hLen_supp, ← h_edges_len]; omega) =
                          w.support[km1 + 1]'(by rw [hLen_supp]; omega) := by
                  rw [← ha_snd]; exact hk_eq.symm
                exact (List.Nodup.getElem_inj_iff hNodup).mp h1
              have h_i_eq : i = km1 := by omega
              rw [hb'_fst]
              have h_supp_eq_bp :
                  w.support[i]'(by rw [hLen_supp, ← h_edges_len]; omega) = bp := by
                rw [hbp_val]; congr 1
              exact h_supp_eq_bp
    · -- A.1: M-edge not on walk. Partner = b_star.
      refine ⟨b_star, ?_, ?_⟩
      · -- xorWith.Adj a b_star: G.Adj ∧ (M.Adj iff s ∉ walk).
        exact ⟨M.adj_sub hM_b_star, ⟨fun _ => h_walk_M, fun _ => hM_b_star⟩⟩
      · -- Uniqueness.
        intro b' h_b'_adj
        obtain ⟨_, h_iff⟩ := h_b'_adj
        by_cases h_M_b' : M.Adj a b'
        · exact hM_unique b' h_M_b'
        · -- ¬M.Adj a b' → s(a, b') ∈ walk → a ∈ walk.support
          --   → by M_partner_is_walk_neighbor, s(a, b_star) ∈ walk. Contradicts h_walk_M.
          exfalso
          have h_s_in : s(a, b') ∈ w.edges := by
            by_contra h
            exact h_M_b' (h_iff.mpr h)
          have h_a_in_support : a ∈ w.support := w.fst_mem_support_of_mem_edges h_s_in
          exact h_walk_M
            (hw.M_partner_is_walk_neighbor hM h_a_in_support ha_ne_u ha_ne_v hM_b_star)
  · -- Case B: a ∉ M.verts. a ∈ walk.support, a is endpoint.
    have hSupp : a ∈ w.support := by
      rcases ha with h | h
      · exact absurd h hMv
      · exact h
    have h_endpoint : a = u ∨ a = v := by
      by_contra h
      apply hMv
      apply hw.interior_in_M_verts hSupp
      · intro h_u; exact h (Or.inl h_u)
      · intro h_v; exact h (Or.inr h_v)
    -- w has length ≥ 1, so darts[0] and darts[length-1] exist.
    have h_pos_len : 0 < w.length := hw.nonEmpty
    have h_dart0_lt : 0 < w.darts.length := by rw [w.length_darts]; exact h_pos_len
    have h_dart_last_lt : w.length - 1 < w.darts.length := by
      rw [w.length_darts]; omega
    rcases h_endpoint with h_eq_u | h_eq_v
    · -- B.1: a = u (start). Partner = w.support[1] (= darts[0].snd).
      subst h_eq_u
      -- Partner: (w.darts[0]).snd = w.support[1].
      have h_succ_lt : 1 < w.support.length := by rw [hLen_supp]; omega
      refine ⟨w.support[1]'h_succ_lt, ?_, ?_⟩
      · -- xorWith.Adj a (support[1]).
        refine ⟨?_, ?_⟩
        · -- G.Adj a (support[1]).
          have h_dart_adj : G.Adj (w.darts[0]'h_dart0_lt).fst (w.darts[0]'h_dart0_lt).snd :=
            (w.darts[0]'h_dart0_lt).adj
          have h_fst : (w.darts[0]'h_dart0_lt).fst = a := by
            rw [w.fst_darts_getElem h_dart0_lt, List.getElem_dropLast]
            exact w.support_getElem_zero
          have h_snd : (w.darts[0]'h_dart0_lt).snd = w.support[1]'h_succ_lt := by
            rw [w.snd_darts_getElem h_dart0_lt, List.getElem_tail]
          rw [h_fst, h_snd] at h_dart_adj
          exact h_dart_adj
        · -- M.Adj a (support[1]) iff s(a, support[1]) ∉ walk.
          -- M.Adj false (a unmatched). s(a, support[1]) is edges[0], ∈ walk.
          -- iff: false ↔ false = true.
          constructor
          · intro h_M_a_s1
            exact absurd (M.edge_vert h_M_a_s1) hw.startUnmatched
          · intro h_notin
            exfalso
            apply h_notin
            -- s(a, support[1]) = edges[0]. Use walk_edge_eq_support.
            have h_e0_lt : 0 < w.edges.length := by rw [h_edges_len]; exact h_pos_len
            have h_e0_eq : w.edges[0]'h_e0_lt = s(w.support[0]'(by rw [hLen_supp]; omega),
                                                w.support[1]'h_succ_lt) := by
              exact walk_edge_eq_support w 0 h_e0_lt
            rw [w.support_getElem_zero] at h_e0_eq
            rw [← h_e0_eq]
            exact List.getElem_mem _
      · -- Uniqueness.
        intro b' h_b'_adj
        obtain ⟨_, h_iff⟩ := h_b'_adj
        have h_M_b'_false : ¬ M.Adj a b' := fun h =>
          hw.startUnmatched (M.edge_vert h)
        have h_s_in : s(a, b') ∈ w.edges := by
          by_contra h
          exact h_M_b'_false (h_iff.mpr h)
        -- s(a, b') ∈ w.edges. Find position i.
        rcases List.getElem_of_mem h_s_in with ⟨i, hi_lt, hi_eq⟩
        have h_dart_lt' : i < w.darts.length := by
          rw [w.length_darts, ← h_edges_len]; exact hi_lt
        have h_e_form := walk_edge_eq_support w i hi_lt
        -- s(a, b') = s(support[i], support[i+1]).
        rw [h_e_form] at hi_eq
        -- a = support[i] or a = support[i+1].
        rcases Sym2.eq_iff.mp hi_eq.symm with ⟨ha_fst, hb'_snd⟩ | ⟨ha_snd, hb'_fst⟩
        · -- a = support[i]. By Nodup, i = 0.
          have h_i_eq : i = 0 := by
            have h1 : w.support[i]'(by rw [hLen_supp]; rw [← h_edges_len]; omega) =
                      w.support[0]'(by rw [hLen_supp]; omega) := by
              rw [← ha_fst]; exact w.support_getElem_zero.symm
            exact (List.Nodup.getElem_inj_iff hNodup).mp h1
          -- So b' = support[i+1] = support[1].
          subst h_i_eq
          exact hb'_snd
        · -- a = support[i+1]. By Nodup, i+1 = 0, impossible.
          exfalso
          have h_i_eq : i + 1 = 0 := by
            have h1 : w.support[i+1]'(by rw [hLen_supp]; rw [← h_edges_len]; omega) =
                      w.support[0]'(by rw [hLen_supp]; omega) := by
              rw [← ha_snd]; exact w.support_getElem_zero.symm
            exact (List.Nodup.getElem_inj_iff hNodup).mp h1
          omega
    · -- B.2: a = v (end). Partner = w.support[w.length - 1] (= darts[length-1].fst).
      subst h_eq_v
      -- Use Lm := w.length - 1 with Lm + 1 = w.length.
      obtain ⟨Lm, hL_eq⟩ : ∃ Lm, w.length = Lm + 1 := ⟨w.length - 1, by omega⟩
      have h_dart_Lm_lt : Lm < w.darts.length := by rw [w.length_darts, hL_eq]; omega
      have h_supp_Lm_lt : Lm < w.support.length := by rw [hLen_supp, hL_eq]; omega
      have h_supp_Lm_succ_lt : Lm + 1 < w.support.length := by rw [hLen_supp, hL_eq]; omega
      refine ⟨w.support[Lm]'h_supp_Lm_lt, ?_, ?_⟩
      · -- xorWith.Adj a (support[Lm]).
        refine ⟨?_, ?_⟩
        · -- G.Adj a (support[Lm]).
          have h_dart_adj : G.Adj (w.darts[Lm]'h_dart_Lm_lt).fst
                                  (w.darts[Lm]'h_dart_Lm_lt).snd :=
            (w.darts[Lm]'h_dart_Lm_lt).adj
          have h_fst : (w.darts[Lm]'h_dart_Lm_lt).fst = w.support[Lm]'h_supp_Lm_lt := by
            rw [w.fst_darts_getElem h_dart_Lm_lt, List.getElem_dropLast]
          have h_snd : (w.darts[Lm]'h_dart_Lm_lt).snd = a := by
            rw [w.snd_darts_getElem h_dart_Lm_lt, List.getElem_tail]
            -- support[Lm + 1] = support[w.length] = v = a.
            have : (w.support[Lm + 1]'h_supp_Lm_succ_lt : V) =
                   w.support[w.length]'(by rw [hLen_supp]; omega) := by
              congr 1
              exact hL_eq.symm
            rw [this]
            exact w.support_getElem_length
          rw [h_fst, h_snd] at h_dart_adj
          exact h_dart_adj.symm
        · -- M.Adj a (support[Lm]) iff s(a, support[Lm]) ∉ walk.
          constructor
          · intro h_M
            exact absurd (M.edge_vert h_M) hw.endUnmatched
          · intro h_notin
            exfalso
            apply h_notin
            -- s(a, support[Lm]) = edges[Lm].
            have h_eLm_lt : Lm < w.edges.length := by rw [h_edges_len, hL_eq]; omega
            have h_eLm : w.edges[Lm]'h_eLm_lt = s(w.support[Lm]'h_supp_Lm_lt,
                                                  w.support[Lm + 1]'h_supp_Lm_succ_lt) :=
              walk_edge_eq_support w Lm h_eLm_lt
            -- support[Lm+1] = a.
            have h_supp_succ_eq_a : w.support[Lm + 1]'h_supp_Lm_succ_lt = a := by
              have : (w.support[Lm + 1]'h_supp_Lm_succ_lt : V) =
                     w.support[w.length]'(by rw [hLen_supp]; omega) := by
                congr 1; exact hL_eq.symm
              rw [this]
              exact w.support_getElem_length
            rw [h_supp_succ_eq_a] at h_eLm
            -- h_eLm : edges[Lm] = s(support[Lm], a)
            -- Want: s(a, support[Lm]) ∈ w.edges.
            rw [show s(a, w.support[Lm]'h_supp_Lm_lt) =
                    s(w.support[Lm]'h_supp_Lm_lt, a) from Sym2.eq_swap]
            rw [← h_eLm]
            exact List.getElem_mem _
      · -- Uniqueness.
        intro b' h_b'_adj
        obtain ⟨_, h_iff⟩ := h_b'_adj
        have h_M_b'_false : ¬ M.Adj a b' := fun h =>
          hw.endUnmatched (M.edge_vert h)
        have h_s_in : s(a, b') ∈ w.edges := by
          by_contra h
          exact h_M_b'_false (h_iff.mpr h)
        rcases List.getElem_of_mem h_s_in with ⟨i, hi_lt, hi_eq⟩
        have h_dart_lt' : i < w.darts.length := by
          rw [w.length_darts, ← h_edges_len]; exact hi_lt
        have h_e_form := walk_edge_eq_support w i hi_lt
        rw [h_e_form] at hi_eq
        rcases Sym2.eq_iff.mp hi_eq.symm with ⟨ha_fst, hb'_snd⟩ | ⟨ha_snd, hb'_fst⟩
        · -- a = support[i]. By Nodup, i = w.length.
          exfalso
          have h_i_eq : i = w.length := by
            have h1 : w.support[i]'(by rw [hLen_supp, ← h_edges_len]; omega) =
                      w.support[w.length]'(by rw [hLen_supp]; omega) := by
              rw [← ha_fst]; exact w.support_getElem_length.symm
            exact (List.Nodup.getElem_inj_iff hNodup).mp h1
          -- But i < w.edges.length = w.length. So i < w.length but i = w.length. ⊥.
          omega
        · -- a = support[i+1]. By Nodup, i+1 = w.length, so i = w.length - 1 = Lm.
          have h_i_succ_eq : i + 1 = w.length := by
            have h1 : w.support[i+1]'(by rw [hLen_supp, ← h_edges_len]; omega) =
                      w.support[w.length]'(by rw [hLen_supp]; omega) := by
              rw [← ha_snd]; exact w.support_getElem_length.symm
            exact (List.Nodup.getElem_inj_iff hNodup).mp h1
          have h_i_eq_Lm : i = Lm := by omega
          subst h_i_eq_Lm
          exact hb'_fst

/-! ### Helpers for the cardinality lemma -/

/-- For a list where consecutive entries alternate in their membership of `M`
    and the first entry is not in `M`, exactly half (floored) of the entries
    are in `M`. -/
private lemma list_filter_count_of_alternating_aux {α : Type*} (M : Set α)
    [DecidablePred (· ∈ M)] :
    ∀ (n : ℕ) (l : List α), l.length = n →
      (∀ (h : 0 < l.length), l[0]'h ∉ M) →
      (∀ i (hi : i + 1 < l.length),
        (l[i]'(Nat.lt_of_succ_lt hi) ∈ M) ≠ (l[i+1]'hi ∈ M)) →
      (l.filter (· ∈ M)).length = l.length / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen h_first h_alt
    match l, hlen with
    | [], _ => simp
    | [a], _ =>
      have ha : a ∉ M := h_first (by simp)
      simp [List.filter_cons, decide_eq_true_iff, ha]
    | a :: b :: rest, hlen' =>
      have ha : a ∉ M := h_first (by simp)
      have h_alt_0 : (a ∈ M) ≠ (b ∈ M) := by
        have := h_alt 0 (by simp)
        simpa using this
      have hb : b ∈ M := by
        by_contra hbN
        apply h_alt_0
        exact propext (Iff.intro (fun h => absurd h ha) (fun h => absurd h hbN))
      have h_rest_first : ∀ (h : 0 < rest.length), rest[0]'h ∉ M := by
        intro h
        have h_alt_1 : (b ∈ M) ≠ (rest[0]'h ∈ M) := by
          have ha2 : 1 + 1 < (a :: b :: rest).length := by simp; omega
          have := h_alt 1 ha2
          simpa using this
        intro hM
        exact h_alt_1
          (propext (Iff.intro (fun _ => hM) (fun _ => hb)))
      have h_rest_alt : ∀ i (hi : i + 1 < rest.length),
          (rest[i]'(Nat.lt_of_succ_lt hi) ∈ M) ≠ (rest[i+1]'hi ∈ M) := by
        intro i hi
        have h_a := h_alt (i + 2) (by simp; omega)
        simpa using h_a
      have h_rest_len_lt : rest.length < n := by simp at hlen'; omega
      have ih_rest := ih rest.length h_rest_len_lt rest rfl h_rest_first h_rest_alt
      have h_filter_eq :
          (a :: b :: rest).filter (· ∈ M) = b :: rest.filter (· ∈ M) := by
        simp [List.filter_cons, decide_eq_true_iff, ha, hb]
      rw [h_filter_eq]
      simp only [List.length_cons]
      rw [ih_rest]
      omega

private lemma list_filter_count_of_alternating {α : Type*} (M : Set α)
    [DecidablePred (· ∈ M)] (l : List α)
    (h_first : ∀ (h : 0 < l.length), l[0]'h ∉ M)
    (h_alt : ∀ i (hi : i + 1 < l.length),
      (l[i]'(Nat.lt_of_succ_lt hi) ∈ M) ≠ (l[i+1]'hi ∈ M)) :
    (l.filter (· ∈ M)).length = l.length / 2 :=
  list_filter_count_of_alternating_aux M l.length l rfl h_first h_alt

/-- A bridge lemma: for an `M`-augmenting walk `w`, the walk has `w.length / 2`
    edges in `M`, counted via the list filter. -/
private lemma IsAugmenting.length_filter_eq
    {M : G.Subgraph} {u v : V} {w : G.Walk u v} (hw : IsAugmenting M w) :
    letI : DecidablePred (· ∈ M.edgeSet) := Classical.decPred _
    (w.edges.filter (· ∈ M.edgeSet)).length = w.length / 2 := by
  classical
  rw [← w.length_edges]
  apply list_filter_count_of_alternating
  · -- First edge ∉ M.
    intro hpos
    have h_edges_pos : 0 < w.edges.length := hpos
    have h_pos_walk : 0 < w.length := by
      rw [← w.length_edges]; exact h_edges_pos
    have h_supp : w.support[0]'(by rw [w.length_support]; omega) = u :=
      w.support_getElem_zero
    have h_supp_1 : 1 < w.support.length := by rw [w.length_support]; omega
    have h_edge_form := walk_edge_eq_support w 0 h_edges_pos
    rw [h_supp] at h_edge_form
    rw [h_edge_form]
    intro hMem
    have hMab : M.Adj u (w.support[1]'h_supp_1) := Subgraph.mem_edgeSet.mp hMem
    exact hw.startUnmatched (M.edge_vert hMab)
  · -- Alternation.
    intro i hi
    exact hw.alternating (i := i) hi

/-- The walk-edges set, as a `Set (Sym2 V)`, has `ncard` equal to `w.length`
    when the walk is a path (edges are distinct). -/
private lemma walk_edges_set_ncard_eq
    {u v : V} (w : G.Walk u v) (hp : w.IsPath) :
    ({e | e ∈ w.edges} : Set (Sym2 V)).ncard = w.length := by
  classical
  have h_nodup : w.edges.Nodup := hp.edges_nodup
  have h_eq : ({e | e ∈ w.edges} : Set (Sym2 V)) =
              (w.edges.toFinset : Set (Sym2 V)) := by
    ext e
    simp
  rw [h_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup h_nodup,
      w.length_edges]

/-- The intersection of `M.edgeSet` with the walk-edges set has `ncard` equal
    to `(w.edges.filter (· ∈ M.edgeSet)).length`. -/
private lemma M_inter_walk_edges_ncard
    {M : G.Subgraph} {u v : V} (w : G.Walk u v) (hp : w.IsPath) :
    letI : DecidablePred (· ∈ M.edgeSet) := Classical.decPred _
    (M.edgeSet ∩ {e | e ∈ w.edges}).ncard =
      (w.edges.filter (· ∈ M.edgeSet)).length := by
  classical
  -- The set equals (filter result).toFinset as a Set.
  have h_nodup : w.edges.Nodup := hp.edges_nodup
  have h_filter_nodup : (w.edges.filter (· ∈ M.edgeSet)).Nodup := h_nodup.filter _
  have h_set_eq : (M.edgeSet ∩ {e | e ∈ w.edges} : Set (Sym2 V)) =
                  ((w.edges.filter (· ∈ M.edgeSet)).toFinset : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
               List.mem_toFinset, List.mem_filter, decide_eq_true_iff,
               Finset.mem_coe]
    tauto
  rw [h_set_eq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup h_filter_nodup]

/--
**Augmentation lemma (cardinality).** If `w` is `M`-augmenting and `M` has
finitely many edges, then `xorWith M w` has exactly one more edge than `M`. -/
theorem IsAugmenting.xorWith_card
    {M : G.Subgraph} (hM : M.IsMatching) {u v : V}
    {w : G.Walk u v} (hw : IsAugmenting M w) (hMFin : M.edgeSet.Finite) :
    (xorWith M w).edgeSet.ncard = M.edgeSet.ncard + 1 := by
  classical
  -- Step 0: w.length is odd.
  have h_odd : Odd w.length := by
    -- This is the odd-length lemma from Matching.lean, proved as an example there.
    -- Inline a self-contained proof here.
    have hlen : 1 ≤ w.length := hw.nonEmpty
    have hLE : w.edges.length = w.length := w.length_edges
    have hpos : 0 < w.edges.length := by rw [hLE]; exact hlen
    have hEdgesNonempty : w.edges ≠ [] := List.length_pos_iff.mp hpos
    have h_first : (w.edges[0]'hpos) ∉ M.edgeSet := by
      revert hpos
      cases w with
      | nil => intro hpos; simp at hpos
      | @cons a b c hadj p =>
        intro _
        simp only [Walk.edges_cons, List.getElem_cons_zero]
        intro hMem
        exact hw.startUnmatched (M.edge_vert (Subgraph.mem_edgeSet.mp hMem))
    have hLastEdge : w.edges.getLast hEdgesNonempty = s(w.penultimate, v) :=
      Walk.getLast_edges_eq_mk_penultimate_end _
    have h_last : (w.edges[w.edges.length - 1]'(by omega)) ∉ M.edgeSet := by
      have hEq : w.edges[w.edges.length - 1]'(by omega)
          = w.edges.getLast hEdgesNonempty := by
        rw [List.getLast_eq_getElem]
      rw [hEq, hLastEdge]
      intro hMem
      apply hw.endUnmatched
      exact M.mem_verts_of_mem_edge hMem (by simp [Sym2.mem_iff])
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
        have hAltLocal :
            (w.edges[k]'hk ∈ M.edgeSet) ≠ (w.edges[k+1]'hi ∈ M.edgeSet) :=
          hw.alternating hi
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
          have hNotOddK : ¬ Odd k := fun hOdd =>
            (Nat.not_odd_iff_even.mpr hEvenK) hOdd
          have h_k_notIn : w.edges[k]'hk ∉ M.edgeSet := fun hMem =>
            hNotOddK (ihk.mp hMem)
          by_contra hSuccNotIn
          apply hAltLocal
          exact propext (Iff.intro (fun hKin => absurd hKin h_k_notIn)
                                    (fun hSuccIn => absurd hSuccIn hSuccNotIn))
    have hLastIff := hKey (w.edges.length - 1) (by omega)
    have hNotOddLast : ¬ Odd (w.edges.length - 1) :=
      fun hO => h_last (hLastIff.mpr hO)
    rcases Nat.even_or_odd (w.edges.length - 1) with hE | hO
    · rw [← hLE]
      rcases hE with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    · exact absurd hO hNotOddLast
  -- Step 1: Set up A, B, and prove (xorWith M w).edgeSet = (A \ B) ∪ (B \ A).
  set A : Set (Sym2 V) := M.edgeSet with hAdef
  set B : Set (Sym2 V) := {e | e ∈ w.edges} with hBdef
  have hBFin : B.Finite := by
    rw [hBdef]
    exact w.edges.finite_toSet
  have hAFin : A.Finite := hMFin
  have hAB_inter_fin : (A ∩ B).Finite := hAFin.inter_of_left B
  have h_xor_eq : (xorWith M w).edgeSet = (A \ B) ∪ (B \ A) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [Subgraph.mem_edgeSet]
      show (xorWith M w).Adj a b ↔ _
      change G.Adj a b ∧ (M.Adj a b ↔ s(a, b) ∉ w.edges) ↔ _
      simp only [Set.mem_union, Set.mem_diff, hAdef, hBdef, Set.mem_setOf_eq,
                 Subgraph.mem_edgeSet]
      constructor
      · rintro ⟨_, hAdj_iff⟩
        by_cases hMab : M.Adj a b
        · left
          exact ⟨hMab, hAdj_iff.mp hMab⟩
        · right
          have h_walk : s(a, b) ∈ w.edges := by
            by_contra hN
            exact hMab (hAdj_iff.mpr hN)
          exact ⟨h_walk, hMab⟩
      · rintro (⟨hMab, h_notin⟩ | ⟨h_in, h_notM⟩)
        · refine ⟨M.adj_sub hMab, ?_⟩
          exact ⟨fun _ => h_notin, fun _ => hMab⟩
        · have hG_ab : G.Adj a b := w.adj_of_mem_edges h_in
          refine ⟨hG_ab, ?_⟩
          exact ⟨fun hMab => absurd hMab h_notM, fun h => absurd h_in h⟩
  -- Step 2: ncard arithmetic. (A \ B) and (B \ A) are disjoint.
  rw [h_xor_eq]
  have h_disj : Disjoint (A \ B) (B \ A) := by
    rw [Set.disjoint_left]
    rintro e ⟨_, heNB⟩ ⟨heB, _⟩
    exact heNB heB
  have h_AB_fin : (A \ B).Finite := hAFin.subset Set.diff_subset
  have h_BA_fin : (B \ A).Finite := hBFin.subset Set.diff_subset
  rw [Set.ncard_union_eq h_disj h_AB_fin h_BA_fin]
  -- Step 3: Cardinalities of A \ B and B \ A via A ∩ B.
  -- (A \ B).ncard = A.ncard - (A ∩ B).ncard.
  -- (B \ A).ncard = B.ncard - (A ∩ B).ncard.
  have hABdiff_eq : (A \ B).ncard = A.ncard - (A ∩ B).ncard := by
    have := Set.ncard_inter_add_ncard_diff_eq_ncard A B hAFin
    omega
  have hBAdiff_eq : (B \ A).ncard = B.ncard - (A ∩ B).ncard := by
    have h1 := Set.ncard_inter_add_ncard_diff_eq_ncard B A hBFin
    have h2 : (B ∩ A).ncard = (A ∩ B).ncard := by
      rw [Set.inter_comm]
    omega
  rw [hABdiff_eq, hBAdiff_eq]
  -- Step 4: B.ncard = w.length, (A ∩ B).ncard = w.length / 2.
  have hB_card : B.ncard = w.length := by
    rw [hBdef]; exact walk_edges_set_ncard_eq w hw.isPath
  have hAB_card : (A ∩ B).ncard = w.length / 2 := by
    rw [hAdef, hBdef, M_inter_walk_edges_ncard w hw.isPath,
        hw.length_filter_eq]
  rw [hB_card, hAB_card]
  -- Step 5: (A.ncard - L/2) + (L - L/2) = A.ncard + 1, using L odd.
  -- L = 2k+1, so L/2 = k, L - L/2 = k+1, A.ncard - k + k + 1 = A.ncard + 1
  -- (assuming A.ncard ≥ L/2, but A ∩ B ⊆ A so this follows).
  have h_inter_le_A : (A ∩ B).ncard ≤ A.ncard :=
    Set.ncard_le_ncard Set.inter_subset_left hAFin
  rw [hAB_card] at h_inter_le_A
  obtain ⟨k, hk⟩ := h_odd
  omega

end Hackathon
