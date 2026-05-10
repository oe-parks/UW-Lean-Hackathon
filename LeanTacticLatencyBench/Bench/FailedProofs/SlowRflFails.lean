/-!
# Bench: slow `rfl` that fails

`rfl` is asked to prove `2^25 + 1 = 2^25`. The kernel reduces both
sides via `Nat.pow`, which is exponential-shape in the exponent for
this representation. After several seconds it concludes the two
sides are not definitionally equal and reports failure.
-/

example : 2^25 + 1 = 2^25 := by rfl
