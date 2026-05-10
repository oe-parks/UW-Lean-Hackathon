/-!
# Bench: a file we will edit while the server is busy

The "slow" version of this file does heavy kernel reduction in a
`have` clause; the "fast" replacement is `trivial`. Our LSP harness
sends the slow version via `didOpen`, waits a brief moment, and then
sends a `didChange` that swaps in the fast version. The metric we
care about is "from `didChange` to fresh `publishDiagnostics`".

The actual file contents start as `trivial`; the harness rewrites
in-memory.
-/

example : True := trivial
