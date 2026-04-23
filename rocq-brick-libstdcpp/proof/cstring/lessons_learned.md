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
- Match the abstraction to the API surface. Null-terminated string functions
  want a string predicate such as `cstring.R`; counted byte APIs want a counted
  byte predicate such as `object_bytesR`, not a string predicate with an
  accidental terminator interpretation.
- Keep undefined behavior out of the contract. The precondition should rule out
  malformed inputs rather than silently assigning them behavior. For strings,
  that means a reachable terminator. For byte APIs, that means a valid
  byte-counted range and any extra side conditions the textual spec requires.
- When a standard API is phrased in terms of object representation bytes, avoid
  overspecifying the storage type. An abstract byte predicate is closer to the
  text than a spec that insists on a concrete `unsigned char[]` object.
- Prefer exact active-range specs over built-in `take`/`drop` bookkeeping in
  the library contract. Let clients partition larger buffers into “active
  prefix” and “rest” themselves.

## Proofs

- Prefer general arithmetic cleanup over test-specific proof hacks. If a proof
  needs to reconcile different representations of the same number, first ask
  whether the model can produce an arithmetic expression that
  `Arith.arith_simpl` can normalize. Avoid local tactics that know about one
  test's concrete offsets or string literals.
- `ego` is not always redundant after `go`. In these litmus proofs it often
  discharges pure obligations from `assert` statements and pointer comparisons.
  It is worth testing removals with `dune`, but keep `ego` where the generated
  assertion proof obligations remain.
- Prefer `rewrite /foo` over `cbn [foo]` / `cbv [foo]` when peeling a small
  wrapper. It keeps the proof script closer to the intended abstraction level
  and avoids collateral simplification.
- Default proof imports can materially change the shape of generated array
  resources. When imports change, re-check whether stack arrays arrive as
  `arrayLR`, unlocked `arrayR`, or borrowed-cell continuations before trying to
  reuse an older proof literally.
- Small bridge lemmas pay for themselves. Conversions such as
  `arrayLR`-to-`cstring.R`, `object_bytesR`-to-`arrayLR`, prefix/tail split
  lemmas, and byte-array-to-`anyR` lemmas remove duplicated Iris bookkeeping
  and make later litmus proofs much easier to repair.
- When automation stops just short of a goal, first check whether the proof is
  missing a resource-shape bridge rather than a stronger tactic. Several recent
  repairs were really about rebuilding the exact array or byte-view predicate
  that `go` expected.
- For `memmove`, non-overlap and overlap are not merely proof variants. If the
  spec itself presents disjoint source and destination ownership, overlapping
  clients are blocked at the specification level and need a different contract,
  not just a more clever proof.
