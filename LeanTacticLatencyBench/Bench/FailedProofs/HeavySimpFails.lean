/-!
# Bench: heavy `simp` set with no closure

`simp` is given a long expression and a wide rewrite set (all the
canonical commutativity / associativity / unit lemmas for `Nat` `+` and
`*`), then asked to close a *false* equality. simp tries the rewrite
candidates many times before reporting failure. This is the kind of
pattern users hit when accidentally calling `simp` without the right
side-lemmas.
-/

set_option maxHeartbeats 4000000 in
example (a b c d e f g h i j : Nat) :
    (a + b) * (c + d) * (e + f) * (g + h) * (i + j) =
    (b + a) * (d + c) * (f + e) * (h + g) * (j + i) + 1 := by
  simp [Nat.add_comm, Nat.mul_comm, Nat.add_assoc, Nat.mul_assoc,
        Nat.add_left_comm, Nat.mul_left_comm,
        Nat.zero_add, Nat.add_zero, Nat.zero_mul, Nat.mul_zero,
        Nat.one_mul, Nat.mul_one]
