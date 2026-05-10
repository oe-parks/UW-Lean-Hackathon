/-!
# Bench: slow `decide` that fails

We use `decide` on a long disjunction-of-Nat-equalities. `decide`
reduces each disjunct in turn; the false instance forces reduction of
all branches before reporting failure.
-/

set_option maxRecDepth 4096 in
example :
    let x := 7
    (x = 0) ∨ (x = 1) ∨ (x = 2) ∨ (x = 3) ∨ (x = 4) ∨ (x = 5) ∨ (x = 6) := by
  decide
