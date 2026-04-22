# `<cstring>` Design Notes

## Current Slice

The first supported API slice covers the read-only byte-string functions
`strlen`, `strcmp`, and `strncmp`.

The reusable specs use the existing `cstring.R` abstraction. This keeps the
library-facing contract aligned with existing clients such as `cstdlib::atoi`
and `iostream`: callers provide a pointer to a valid null-terminated C string
whose logical payload is a `cstring.t`.

The ordinary litmus tests for this slice are proven in both
`test/cstring/proof.v` and `test/cstring/proof_old.v`. Embedded-null literal
tests are split into separate functions; they are specified but left admitted
in the active `cstring.R` development, and proven in `proof_old.v` using the
archived lower-level bridge.

## Representation Choice

`cstring.R` remains the active representation for this slice. It describes the
null-terminated string payload itself, not arbitrary storage that may continue
after the first null byte.

This means embedded-null or larger-buffer cases are handled on the client side:
a proof that starts from a larger literal or array resource must split off the
prefix that forms the `cstring.R` argument and frame or later recombine the
remaining bytes. That makes these cases visibly about buffer decomposition
rather than about the semantic contract of read-only cstring functions.

### `arrayR` and `arrayLR`

For hand-written byte-buffer specs and reusable buffer predicates, prefer
`arrayLR` over one-sided `arrayR` or `arrayL` when the surrounding interface
leaves us that choice. The two-sided predicate usually preserves more useful
ownership information for clients that both read and later restore or mutate a
buffer.

The current explicit `char[]` litmus tests are slightly different: cpp2v
generates stack-array initializer resources as concrete `arrayR` predicates.
Their proofs therefore use local `arrayR` splitting/recombination lemmas to
match the generated proof state directly. This should not be read as a general
preference for `arrayR` in library specs; it is a proof-local accommodation for
the shape of generated stack-buffer resources.

## Archived Alternative

The earlier experiment introduced a lower-level `cstringz.R q s tail` predicate
for concrete character arrays shaped like:

```text
cstring.to_zstring s ++ tail
```

That variant is preserved in:

- `model_old.v`
- `pred_old.v`
- `spec_old.v`
- `test/cstring/proof_old.v`

Those files are kept for comparison or rollback while we proceed with the
`cstring.R`-based active design.

## Leftover Tasks

- Transfer the string-literal embedded-null proof bridge from
  `test/cstring/proof_old.v` to the active `test/cstring/proof.v` when we want
  to discharge the currently admitted literal tests without depending on
  `pred_old.v`. The active array-buffer proofs already cover the analogous
  `char[]` client-side splitting pattern.
- Optionally extend `test/cstring/proof_old.v` with the explicit `char[]`
  array-buffer litmus proofs if we later want side-by-side regression coverage
  for the archived `cstringz.R` design. For now the active and archived proof
  files are intentionally not kept in lockstep.
- Consider whether cpp2v should generate `arrayLR` rather than `arrayR` for
  stack-allocated array initializers, or provide a standard bridge for this
  case. The active `char[]` proofs use local `arrayR` helpers only because the
  generated proof state has that shape.
- Keep undefined behavior out of green specs and tests: no null pointers,
  invalid pointers, or arrays without a reachable null terminator.
- Use the existing mutable cstring buffer support, especially `cstring.bufR`,
  when specifying functions such as `strcpy`, `strncpy`, `strcat`, and
  `strncat`; revisit only if these predicates are not expressive enough.
