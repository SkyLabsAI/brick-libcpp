# Lessons Learned

These notes collect reusable lessons from the `<cstring>` specification work.
They are meant to be broader than the current litmus tests and suitable for
later promotion into shared docs.

## Models

- Prefer model expressions that normalize under standard arithmetic cleanup.
  For pointer offsets and numeric return values, expressions such as
  `(1 + off)%Z` are easier for `Arith.arith_simpl` and downstream symbolic
  execution than structurally equivalent constructors such as `Z.succ off`.
  This keeps proofs portable across callers instead of requiring literal-
  specific normalization steps.
- Add small `Succeed Example` checks for model functions. They are cheap
  regression tests for corner cases such as empty needles, terminating null
  characters, missing characters, and first-versus-last occurrence behavior.

## Specifications

- Use small notations or helper definitions in `spec.v` to translate model
  results into return values when this preserves the abstraction boundary. The
  `search_result` pattern keeps null-versus-offset pointer results local to the
  specs rather than leaking pointer arithmetic into the pure model.

## Proofs

- Prefer general arithmetic cleanup over test-specific proof hacks. If a proof
  needs to reconcile different representations of the same number, first ask
  whether the model can produce an arithmetic expression that `Arith.arith_simpl`
  can normalize. Avoid local tactics that know about one test's concrete
  offsets or string literals.
- `ego` is not always redundant after `go`. In these litmus proofs it often
  discharges pure obligations from `assert` statements and pointer comparisons.
  It is worth testing removals with `dune`, but keep `ego` where the generated
  assertion proof obligations remain.
