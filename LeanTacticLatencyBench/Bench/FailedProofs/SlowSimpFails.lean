/-!
# Bench: slow `simp` that fails (no progress + many lemmas)

We feed `simp` a small AC-rewrite system and ask it to prove a goal
that simp cannot close. simp tries each rewrite, makes no progress on
the equality, and reports failure ("simp made no progress" or "unsolved
goals"). The pile-up of attempted rewrites makes this slow on a long
sum.
-/

set_option maxHeartbeats 4000000 in
example (a b c d e f g h i j : Nat) :
    a + b + c + d + e + f + g + h + i + j =
    j + i + h + g + f + e + d + c + b + a + 1 := by
  simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
