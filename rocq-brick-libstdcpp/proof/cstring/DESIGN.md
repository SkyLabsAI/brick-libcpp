# `<cstring>` Design Notes

## Current State

The active development now has two substantial slices:

- null-terminated byte-string operations specified against `cstring.R`:
  `strlen`, `strcmp`, `strncmp`, `strchr`, `strrchr`, `strspn`, `strcspn`,
  `strpbrk`, and `strstr`;
- counted byte-array operations specified against abstract object-byte
  predicates: `memchr`, `memcmp`, `memset`, `memcpy`, and `memmove`.

The string slice keeps the reusable library-facing contract aligned with the
existing `cstring.R` abstraction: callers provide a pointer to a valid
null-terminated C string whose logical payload is a `cstring.t`.

The counted byte slice uses abstract byte predicates rather than `cstring.R`.
These operations are not about null-terminated strings, and embedded zero
bytes are ordinary data.

On the client side, the active proof files currently prove:

- `test/cstring/proof.v` proves the ordinary `strlen` / `strcmp` / `strncmp`
  litmus tests, the active read-only search and segment litmus tests, and the
  explicit `char[]` array-buffer clients for the string slice;
- `test/cstring/proof_mem_functions.v` proves `test_memchr`, `test_memset`,
  `test_memcpy`, `test_memmove`, and `test_memcmp`;
- `test/cstring/proofs_embedded_null.v` proves
  `test_search_embedded_null_array_buffer`, `test_memset_embedded_null`, and
  `test_memchr_embedded_null`.

The archived files `model_old.v`, `pred_old.v`, `spec_old.v`, and
`test/cstring/proof_old.v` are still present for comparison and rollback. They
continue to document the earlier lower-level bridge for literal embedded-null
cases in the string slice.

## Representation Choice

### Null-Terminated Strings

`cstring.R` remains the active representation for the string slice. It
describes the null-terminated payload itself, not arbitrary storage that may
continue after the first null byte.

This means embedded-null or larger-buffer cases are handled on the client side:
a proof that starts from a larger literal or array resource must split off the
prefix that forms the `cstring.R` argument and frame or later recombine the
remaining bytes. That makes these cases visibly about buffer decomposition
rather than about the semantic contract of read-only cstring functions.

### `arrayR` and `arrayLR`

For hand-written buffer specs and reusable buffer predicates, prefer `arrayLR`
over `arrayR` when the surrounding interface leaves us that choice. The
meaning of the letters in these names is framework-specific and should be
documented explicitly elsewhere; what matters here is that `arrayLR` is the
more informative array view for our present clients. The two-sided predicate
tends to preserve the right amount of information for clients that both inspect
and later rebuild or mutate a buffer.

In proofs, however, we must follow the proof state we actually get. With the
current proof imports, `verify_spec; go` often exposes stack arrays as
`arrayLR`, but some local helper steps still interact with `arrayR` after
unlocking or after bridge lemmas. The practical rule is:

- prefer `arrayLR` in specs and reusable bridge lemmas;
- tolerate local `arrayR` reasoning inside proofs when it is simply the
  unlocked form we need to rebuild.

### Counted Byte Arrays

The byte-array slice covers `memchr`, `memcmp`, `memset`, `memcpy`, and
`memmove`. These functions are not null-terminated string functions: embedded
null bytes are ordinary bytes, and the `n` argument determines the whole
relevant range.

For this slice, use counted object-byte views rather than `cstring.R`. The
current public specs use abstract predicates `object_bytesR byte_ty q bytes`
and `object_bytes_anyR byte_ty n`, where `bytes` is the list of unsigned-byte
values observed by the memory operation.

Recent inspection of the framework predicates clarified three important
alternatives:

- `cstring.bufR q sz s` is just `zstring.bufR char_type.Cchar q sz
  (cstring.to_zstring s)`;
- `zstring.bufR` is a string-buffer predicate: it stores a logical string
  payload, requires `zstring.WF`, and also describes a zero-filled tail up to
  the buffer size `sz`;
- `bytesR q xs` is the plain counted-byte predicate
  `arrayR "unsigned char" (fun c => ucharR q c) xs`.

This means `cstring.bufR` and `zstring.bufR` are not suitable definitions of
`object_bytesR`: they are intentionally more structured than the memory
functions require. They model string buffers, not arbitrary object
representations. In contrast, `bytesR` is a much better semantic fit for the
memory-family functions because it represents exactly a counted sequence of
bytes, with no terminator or string well-formedness obligations.

The remaining design question is whether to expose `bytesR` directly in the
specs or to keep a local wrapper such as `object_bytesR`. At the moment the
development still uses the abstract wrapper, but `bytesR` is now the leading
candidate for the eventual underlying definition. If we keep `object_bytesR`,
it should be viewed as an abstraction boundary over a counted-byte predicate,
not as a string-like buffer predicate.

The earlier `byte_ty : type` parameter was introduced as proof-level metadata
for writing interior pointers such as `p.[byte_ty ! i]` in results like
`memchr`. After inspecting the framework predicates, this now looks more like
bookkeeping than semantic content. Since `bytesR` is already fixed to
`"unsigned char"`, a future cleanup may well remove `byte_ty` and standardize
these specs on `Tuchar`-based offsets instead. If `object_bytesR` survives as
an abstraction layer, this proof-level role of `byte_ty` should be documented
near the definition in `pred.v` or `model.v`.

The previous exact-length `arrayLR Tuchar` specs are preserved in a commented
region in `spec.v`. They were useful for bootstrapping the first byte-array
proofs but are too narrow as reusable library specs.

`object_bytesR` and `object_bytes_anyR` are currently parameters rather than
definitions. Existing unsigned-char litmus proofs therefore rely on explicit
bridge laws between concrete arrays and the abstract object-byte predicates.
Future work should either define these wrappers in terms of framework-provided
byte predicates such as `bytesR`, or replace the local bridge axioms with
framework-provided object-representation facts for concrete `char[]`,
`unsigned char[]`, and other trivially copyable objects as needed.

Embedded-null and embedded-zero litmus tests remain useful regression cases. At
present:

- `test_memchr_embedded_null_ok` is proved in the active development;
- `test_memset_embedded_null_ok` is also proved in the active development;
- `test_memcmp_embedded_null`, `test_memcpy_embedded_null`, and
  `test_memmove_embedded_null` are still only declared via `cpp.spec` stubs in
  `test/cstring/proofs_embedded_null.v`.

As with the earlier `cstring.R` pivot, reusable specs should describe ranges of
exactly the length passed to the function. Clients that start from larger
buffers are responsible for partitioning those buffers into the active prefix
and the remaining tail, then recombining the tail after the call. This avoids
putting `take`/`drop` bookkeeping into the library specs themselves.

Use the framework-provided `lengthZ` and `replicateZ` notations from
`skylabs.prelude.list_numbers`; do not define local aliases in `model.v`.

### Character Arguments

Functions such as `strchr`, `strrchr`, and the memory byte-search routines take
an `int` argument but the textual specifications speak in terms of conversion
to a byte-sized character value. The current specs model only byte-range
arguments via `valid<"unsigned char"> ch`. This is intentionally conservative:
it avoids claiming defined behavior for arguments whose result depends on
implementation choices such as signedness or representable values.

## Archived Alternative

The earlier experiment introduced a lower-level `cstringz.R q s tail`
predicate for concrete character arrays shaped like:

```text
cstring.to_zstring s ++ tail
```

That variant is preserved in:

- `model_old.v`
- `pred_old.v`
- `spec_old.v`
- `test/cstring/proof_old.v`

Those files are kept for comparison or rollback while we proceed with the
active designs based on `cstring.R` and `object_bytesR`.

## Leftover Tasks

- Discharge the remaining embedded-null literal tests in the active
  `cstring.R` development, or leave them intentionally archived-only with a
  clear reason. The archived lower-level bridge in `proof_old.v` remains the
  reference point.
- Decide whether to keep the archived files as a long-lived comparison surface
  or retire them once the active development fully subsumes their distinctive
  coverage.
- Add a short framework-level documentation note somewhere under `docs/`
  explaining the intended meaning and use cases of predicates such as `arrayR`
  and `arrayLR`, since the names are not self-explanatory and easy to
  misdescribe from surface intuition.
- Decide whether the counted-byte specs should switch from the current
  `object_bytesR` wrapper to the existing framework predicate `bytesR`, or
  whether `object_bytesR` should remain as a documented wrapper around it.
- If `object_bytesR` remains, document the exact role of its current
  `byte_ty : type` parameter near the definition and keep that explanation in
  sync with these design notes.
- Investigate whether fractional automation should be derivable automatically
  for abstract object-byte predicates. The current parameterized predicates
  expose fractional behavior axiomatically; the manual split/recombine pattern
  should not spread unchecked.
- Extend the byte-array proofs to the remaining embedded-null regression tests:
  `memcmp`, `memcpy`, and `memmove`.
- Extend the byte-array specs beyond non-overlapping cases. The active
  `memcpy` and `memmove` proofs stay in the disjoint-source/destination lane.
  `test/cstring/proof_mem_functions.v` now carries the `test_memmove_overlap()`
  client stub, but overlapping `memmove` still needs a separate single-buffer
  or otherwise aliased specification that snapshots the source range before
  updating the destination range.
- Keep undefined behavior out of green specs and tests: no null pointers,
  invalid pointers, arrays without a reachable null terminator for string
  functions, or out-of-bounds byte counts for memory functions.
- Use the existing mutable cstring buffer support, especially `cstring.bufR`,
  when specifying functions such as `strcpy`, `strncpy`, `strcat`, and
  `strncat`; revisit only if these predicates are not expressive enough.
