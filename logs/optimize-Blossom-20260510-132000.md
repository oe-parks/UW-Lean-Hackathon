# Optimize log — `Hackathon/GraphIR/Blossom.lean`

**Date:** 2026-05-10 13:20:00  
**Backend:** Claude (Anthropic)  

---

**Baseline:** 6.27s  
**Blocks:** 24 total — 24 optimisable, 0 sorry, 0 error  

---

## [1] `have h_pe_eq : pe = pe' := by`

**Score:** -9.87 → -9.88  
**Time:** 6.27s → 6.17s (+1.6%)  

**Before:**
```lean
have h1 : pe.2 = pe'.2 := (Prod.mk.injEq _ _ _ _).mp heq |>.1
            have h2 : pe.1 = pe'.1 := (Prod.mk.injEq _ _ _ _).mp heq |>.2
            exact Prod.ext h2 h1
```

**After:**
```lean
have h1 : pe.2 = pe'.2 := (Prod.mk.injEq _ _ _ _).mp heq |>.1
            have h2 : pe.1 = pe'.1 := (Prod.mk.injEq _ _ _ _).mp heq |>.2
            exact Prod.ext h2 h1
```

**Why chosen:** best quality score (-9.88).  
**Alternatives considered:**  
- `have h1 : pe.2 = pe'.2 := congr_arg Prod.fst heq            ` — score -9.86 (+0.02 vs chosen), t=6.42s (-0.25s vs chosen)  
- `exact Prod.ext ((Prod.mk.injEq _ _ _ _).mp heq |>.2) ((Prod.` — score 0.65 (+10.53 vs chosen), t=6.49s (-0.32s vs chosen)  

---

## [2] `have h_right : (decide (pe' = pe) || f2 pe') = true := by`

**Score:** 0.62 → -2.37  
**Time:** 6.27s → 6.35s (-2.9%)  

**Before:**
```lean
rw [decide_eq_true h_pe'_eq]; rfl
```

**After:**
```lean
rw [Bool.or_eq_true]
            exact Or.inl (decide_eq_true h_pe'_eq)
```

**Why chosen:** best quality score (-2.37).  
**Alternatives considered:**  
- `rw [decide_eq_true h_pe'_eq]             rfl` — score -0.85 (+1.51 vs chosen), t=6.46s (-0.12s vs chosen)  
- `simp [h_pe'_eq, f2]` — score 8.14 (+10.51 vs chosen), t=6.43s (-0.08s vs chosen)  
- `simp only [Bool.or_eq_true, decide_eq_true_eq]             l` — score 5.14 (+7.51 vs chosen), t=6.44s (-0.09s vs chosen)  

---

## [3] `have h_f2_pe : f2 pe = false := by`

**Score:** -2.37 → -6.86  
**Time:** 6.27s → 6.38s (-0.5%)  

**Before:**
```lean
simp only [f2, List.any_eq_false]
        intro e' he' h_pred
        apply h_pe_unique_in_M' e' he'
        rcases Bool.or_eq_true_iff.mp h_pred with h | h
        · left; exact of_decide_eq_true h
        · right; exact of_decide_eq_true h
```

**After:**
```lean
simp only [f2, List.any_eq_false]
        intro e' he' h_pred
        have h_or := Bool.or_eq_true_iff.mp h_pred
        apply h_pe_unique_in_M' e' he'
        rcases h_or with h_left | h_right
        · left; exact of_decide_eq_true h_left
        · right; exact of_decide_eq_true h_right
```

**Why chosen:** best quality score (-6.86).  
**Alternatives considered:**  
- `simp only [f2, List.any_eq_false] intro e' he' h_pred apply ` — score -2.40 (+4.46 vs chosen), t=6.03s (+0.35s vs chosen)  
- `show M'.any (fun e' => decide (e' = pe) || decide (e' = (pe.` — score 14.14 (+21.00 vs chosen), t=6.36s (+0.02s vs chosen)  

---

## [4] `have h_e_pe' : (decide (e = pe') || decide (e = (pe'.2, pe'.1))) = false := by`

**Score:** -12.86 → -17.37  
**Time:** 6.27s → 6.32s (+0.9%)  

**Before:**
```lean
apply Bool.eq_false_iff.mpr
          intro h_pred
          apply h_e_match
          refine ⟨pe', hpe', ?_⟩
          rcases Bool.or_eq_true_iff.mp h_pred with h | h
          · left; exact of_decide_eq_true h
          · right; exact of_decide_eq_true h
```

**After:**
```lean
apply Bool.eq_false_iff.mpr
          intro h_pred
          have h_or := Bool.or_eq_true_iff.mp h_pred
          apply h_e_match
          refine ⟨pe', hpe', ?_⟩
          rcases h_or with h | h
          · left; exact of_decide_eq_true h
          · right; exact of_decide_eq_true h
```

**Why chosen:** best quality score (-17.37).  
**Alternatives considered:**  
- `apply Bool.eq_false_iff.mpr         intro h_pred         app` — score -12.88 (+4.49 vs chosen), t=6.20s (+0.13s vs chosen)  
- `apply Bool.eq_false_iff.mpr         intro h_pred         app` — score 6.65 (+24.01 vs chosen), t=6.45s (-0.13s vs chosen)  

---

## [5] `have h_last_unm : ¬ Matching.isMatched M (rest.getLast hRestNE) = true := by`

**Score:** -6.87 → -6.89  
**Time:** 6.27s → 6.09s (+3.6%)  

**Before:**
```lean
have h_some : rest.getLast? = some (rest.getLast hRestNE) :=
        List.getLast?_eq_some_getLast _
      rw [h_some] at h_last_block
      exact h_last_block
```

**After:**
```lean
have h_some : rest.getLast? = some (rest.getLast hRestNE) :=
      List.getLast?_eq_some_getLast _
      rw [h_some] at h_last_block
      exact h_last_block
```

**Why chosen:** best quality score (-6.89).  

---

## [6] `theorem isMatching_nil : IsMatching ([] : Matching V) := by`

**Score:** -6.89 → -9.88  
**Time:** 6.27s → 6.22s (-2.1%)  

**Before:**
```lean
refine ⟨?_, ?_, ?_⟩
  · intro e he; cases he
  · intro e₁ he₁; cases he₁
  · exact List.nodup_nil
```

**After:**
```lean
refine ⟨?_, ?_, ?_⟩
  · intro e he; exact he.elim
  · intro e₁ he₁; exact he₁.elim
  · exact List.nodup_nil
```

**Why chosen:** best quality score (-9.88).  
**Alternatives considered:**  
- `refine ⟨fun e he => he.elim, fun e₁ he₁ => he₁.elim, List.no` — score -0.87 (+9.00 vs chosen), t=6.25s (-0.03s vs chosen)  
- `exact ⟨fun _ h => h.elim, fun _ h => h.elim, List.nodup_nil⟩` — score 0.62 (+10.50 vs chosen), t=6.24s (-0.01s vs chosen)  

---

## [7] `have hu' : ¬ B.cycle.contains u' = true := by`

**Score:** -0.88 → -6.88  
**Time:** 6.27s → 6.22s (+0.0%)  

**Before:**
```lean
intro hcyc
      rw [if_pos hcyc] at hu
      rw [← hu] at hu_not
      exact absurd h_stem_in (by rw [hu_not]; simp)
```

**After:**
```lean
intro hcyc
      have h_u_eq_stem : u = B.stem := by rw [← hu]; rw [if_pos hcyc]
      rw [h_u_eq_stem] at hu_not
      exact absurd h_stem_in (by rw [hu_not]; simp)
```

**Why chosen:** best quality score (-6.88).  
**Alternatives considered:**  
- `intro hcyc       rw [if_pos hcyc] at hu       rw [← hu] at h` — score -0.90 (+5.98 vs chosen), t=6.05s (+0.18s vs chosen)  

---

## [8] `have hv' : ¬ B.cycle.contains v' = true := by`

**Score:** -0.88 → -6.88  
**Time:** 6.27s → 6.20s (+0.4%)  

**Before:**
```lean
intro hcyc
      rw [if_pos hcyc] at hv
      rw [← hv] at hv_not
      exact absurd h_stem_in (by rw [hv_not]; simp)
```

**After:**
```lean
intro hcyc
      have h_v_eq_stem : v = B.stem := by rw [← hv]; rw [if_pos hcyc]
      rw [h_v_eq_stem] at hv_not
      exact absurd h_stem_in (by rw [hv_not]; simp)
```

**Why chosen:** best quality score (-6.88).  
**Alternatives considered:**  
- `intro hcyc       rw [if_pos hcyc] at hv       -- hv : B.stem` — score -5.37 (+1.51 vs chosen), t=6.29s (-0.09s vs chosen)  
- `intro hcyc       rw [if_pos hcyc] at hv       -- after rewri` — score -5.36 (+1.52 vs chosen), t=6.44s (-0.24s vs chosen)  

---

## Summary

| | |
|---|---|
| Blocks reviewed | 24 |
| Blocks improved | 8 |
| Baseline runtime | 6.27s |
| Final runtime | 6.20s |
| Time saved | 0.07s (1.1% faster) |
