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
- Predicate and support-lemma interfaces should usually be formulated for
  general permissions `q` and should avoid baking in concrete byte lists,
  offsets, or literal client data unless that specificity is semantically
  essential. Specs may still specialize `q` when the API truly requires full
  ownership, but even then they should remain as general as possible about
  input and output values.

## Proofs

- For arithmetic around list lengths and buffer boundaries, try to stay at the
  `Z` level as long as possible. If that is not enough, next prefer `N`-based
  lemmas and hypotheses. Drop to `nat` only as a last resort. In this
  development, proofs became harder when we rushed downward into `nat`
  conversions instead of reusing the `Z`/`N` structure already present.
- Avoid `Zlength` here; prefer `lengthZ`. In this framework `lengthZ` is
  notation around the `lengthN`-based story, so many `lengthN` lemmas and
  hypotheses can be reused directly with only small interface adjustments.
- Before unfolding a notion, inspect it first with tools such as `Print`,
  `Print Notation`, `Locate`, and `Search`. Several failed cleanup attempts
  came from assuming a familiar definition shape and rewriting toward the wrong
  representation. A quick inspection often shows which arithmetic layer or
  library lemma will actually match.
- In particular, inspect apparently “different” resource predicates before
  designing bridge lemmas or automation around them. In the `memset` read-step
  work, `Print ucharR.` revealed that `ucharR` was already notation for the
  relevant `primR` shape, so the real issue was continuation structure, not a
  missing predicate-conversion lemma.
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
- When proof automation is the goal, directional `_F` / `_B` / `_C`-style
  hints are usually a better fit than borrowing lemmas. Borrowing lemmas are
  continuation-oriented: open a view now, use it locally, and close it later.
  Many reusable BRiCk proof steps are instead directional transformations:
  decompose what is already in context, rebuild a canonical goal shape, or
  replace one resource view by another. Keep semantically meaningful
  split/rebuild steps as ordinary lemmas, and only package them as hints when
  the step is routine enough that proof search should apply it opportunistically.
- For `\cancelx` hints, “provable” and “useful to automation” are different
  thresholds. In this development, some `_guard` and `_using` variants could be
  proved but still did not fire under `go`/`ego` at the relevant call site.
- If a side fact depends on a variable that will only be learned from the
  consumed resources, putting that fact in `\using` may be too early. In such
  cases, ordinary hint parameters or premises can be a better automation
  surface than a more internal-looking `\cancelx` clause.
- Relatedly, ordinary hint parameters can sometimes outperform richer internal
  clause structure. Even when a witness or equality seems conceptually “inside”
  the hint, exposing it as an ordinary premise may let hint search instantiate
  it more effectively.
- That negative lesson has an important complement: if a witness is computable
  from consumed data and the main problem is aligning with the actual
  goal-side parameters, a stronger `_C` hint may still work well if it
  combines:
  - a computation-friendly wrapper premise such as
    `unpack_cstring bytes =[Vm]=> Some (s, tail)`
  - `\bound` variables on the `\proving` side
  - pure `\through` equalities tying those bound variables to the computed
    values
  In the `<cstring>` opener, this was the reformulation that finally let the
  hint fire cleanly under `go`/`ego` without an explicit client-side `Hex`.
- Hint matching is very intensional. A reformulation that replaces compound
  expressions by variables such as `mid` and `k`, together with simple equality
  premises, can fire much more reliably because it matches the post-call proof
  state more directly.
- Reducibility/evaluation-style premises can be a better automation surface
  than plain equalities or existentials when the hint should compute a witness
  from concrete data. In wrapper obligations, converting such a premise with
  `%RedEq_eq` gives back an ordinary equality while keeping the client-facing
  hint surface computation-friendly.
- In the `memset` family, a direct Family A opener can be worthwhile even when
  a more generic wrapper does not fire. Here, `arrayLR_open_prefix_any_C`
  became useful only after its consumed surface was phrased with an explicit
  upper bound `n` instead of `lengthZ bytes`, and it still helped mainly at the
  real `verify_spec` call site rather than on stripped-down toy entailments.
- The Family B read steps ended up working best as reusable ordinary structural
  lemmas plus short explicit proofmode steps, not as auto-firing read hints.
  In particular, `object_bytesR_read_head_uchar_after_open` was a good reusable
  lemma, while several more automated `\cancelx` readback experiments remained
  provable but did not fire usefully under `go`/`ego`.
- For `memset`, Family C also worked better as an explicit closing lemma than
  as opportunistic automation. A local lemma that rebuilds the final
  `arrayLR ... anyR ...` postcondition from a wrapped prefix plus explicit tail
  cells was reusable and stable, without relying on broader close-side hint
  firing.
- In other words: for this proof family, the successful split was
  “Family A opener as automation, Family B readback as ordinary lemmas, Family
  C rebuild as an ordinary lemma”. That is a useful default to try in similar
  byte-API client proofs.
- When automation stops just short of a goal, first check whether the proof is
  missing a resource-shape bridge rather than a stronger tactic. Several recent
  repairs were really about rebuilding the exact array or byte-view predicate
  that `go` expected.
- For `memmove`, non-overlap and overlap are not merely proof variants. If the
  spec itself presents disjoint source and destination ownership, overlapping
  clients are blocked at the specification level and need a different contract,
  not just a more clever proof.
