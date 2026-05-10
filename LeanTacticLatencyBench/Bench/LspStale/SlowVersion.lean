/-!
# Bench: a deliberately slow file for the stale-LSP-cancel harness

Many chained `decide`s on Fin-quantified Booleans force Lean's
elaborator to spend several hundred milliseconds per `have`. By the
time the harness sends `didChange` (a few hundred ms after `didOpen`),
the elaborator is mid-work; we measure how quickly the server cancels
and starts on the new version.

If you find this is *too* slow on a slow machine, drop some of the
`have`s; *too* fast, raise the `Fin` bounds.
-/

set_option maxRecDepth 4096 in
example : True := by
  have h1 : ∀ n : Fin 800, n.val < 1000 := by decide
  have h2 : ∀ n : Fin 800, n.val < 1000 := by decide
  have h3 : ∀ n : Fin 800, n.val < 1000 := by decide
  have h4 : ∀ n : Fin 800, n.val < 1000 := by decide
  have h5 : ∀ n : Fin 800, n.val < 1000 := by decide
  have h6 : ∀ n : Fin 800, n.val < 1000 := by decide
  trivial
