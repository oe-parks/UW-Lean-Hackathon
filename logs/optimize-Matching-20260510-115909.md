# Optimize log — `Hackathon/Graph/Matching.lean`

**Date:** 2026-05-10 11:59:09  
**Backend:** Claude (Anthropic)  

---

**Baseline:** 3.00s  
**Blocks:** 3 total — 3 optimisable, 0 sorry, 0 error  

---

## [1] `example : (⊥ : G.Subgraph).IsMatching := by`

**Score:** 4.80 → -2.70  
**Time:** 3.00s → 3.01s (-0.4%)  

**Before:**
```lean
intro v hv
  simp at hv
```

**After:**
```lean
intro v hv
  exact hv.elim
```

**Why chosen:** best quality score (-2.70).  
**Alternatives considered:**  
- `intro v hv   simp [Subgraph.IsMatching, Subgraph.bot_verts] ` — score 4.80 (+7.50 vs chosen), t=3.04s (-0.03s vs chosen)  
- `intro v hv   exact absurd hv (by simp [Subgraph.verts])` — score 3.30 (+5.99 vs chosen), t=2.95s (+0.06s vs chosen)  

---

## [2] `have h_first : (w.edges[0]'hpos) ∉ M.edgeSet := by`

**Score:** 6.30 → 3.34  
**Time:** 3.00s → 3.36s (-11.6%)  

**Before:**
```lean
revert hpos
    cases w with
    | nil => intro hpos; simp at hpos
    | @cons a b c hadj p =>
      intro _
      simp only [Walk.edges_cons, List.getElem_cons_zero]
      intro hMem
      exact hu (M.edge_vert (Subgraph.mem_edgeSet.mp hMem))
```

**After:**
```lean
cases w with
    | nil => exact absurd hpos (by simp [Walk.edges])
    | @cons a b c hadj p =>
    simp only [Walk.edges_cons, List.getElem_cons_zero]
    intro hMem
    have hVert : a ∈ M.verts := M.edge_vert (Subgraph.mem_edgeSet.mp hMem)
    exact hu hVert
```

**Why chosen:** best quality score (3.34).  
**Alternatives considered:**  
- `revert hpos     cases w with     | nil => intro hpos; simp a` — score 6.30 (+2.97 vs chosen), t=3.04s (+0.32s vs chosen)  
- `cases w with     | nil => exact absurd hpos (by simp)     | ` — score 7.80 (+4.46 vs chosen), t=2.97s (+0.39s vs chosen)  
- `cases w with     | nil =>       simp [Walk.edges] at hpos   ` — score 4.80 (+1.46 vs chosen), t=2.95s (+0.41s vs chosen)  

---

## Summary

| | |
|---|---|
| Blocks reviewed | 3 |
| Blocks improved | 2 |
| Baseline runtime | 3.00s |
| Final runtime | 3.36s |
| Time saved | -0.36s (-12.0% faster) |
