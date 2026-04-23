# `<cstring>` Specification Planning

## Session Context

The goal is to develop BRiCk specifications and litmus tests, with specs and
proofs, for the functions exposed by the C++ `<cstring>` API described by
cppreference.

The intended workflow is iterative:

- familiarize ourselves with the API and textual specification;
- stay consistent with the `brick-libcpp` directory structure;
- propose and revise a plan before carrying out each slice;
- keep litmus tests as `void` functions using suitable `assert` statements
  when possible;
- validate Rocq files through `dune`.

## Current Mental Model

The current workspace contains two active slices and one archived comparison
track.

The active null-terminated byte-string slice covers:

- `model.v` pure models for `strcmp`, `strncmp`, `strchr`, `strrchr`,
  `strspn`, `strcspn`, `strpbrk`, and `strstr`; the active `strlen` spec uses
  the existing `cstring.strlen`;
- `pred.v` reuse of the existing `cstring.R` abstraction for the string slice;
- `spec.v` specs for `strlen`, `strcmp`, `strncmp`, `strchr`, `strrchr`,
  `strspn`, `strcspn`, `strpbrk`, and `strstr` against `cstring.R`;
- `test/cstring/test.cpp` `void` litmus functions using `assert`, including
  separated embedded-null cases and explicit `char[]` array-buffer clients;
- `test/cstring/proof.v` proofs for the ordinary `strlen`, `strcmp`,
  `strncmp`, search/segment tests, array-buffer client tests, and slice-wrapper
  tests;
- `test/cstring/proof_old.v` archived proofs for the earlier lower-level bridge
  design, including literal embedded-null cases.

The active counted byte-array slice covers:

- `pred.v` abstract `object_bytesR` / `object_bytes_anyR` predicates together
  with bridge axioms to and from concrete `arrayLR` byte arrays;
- `spec.v` active specs for `memchr`, `memcmp`, `memset`, `memcpy`, and
  `memmove`, plus a commented archived region containing the earlier
  exact-length `arrayLR Tuchar` versions;
- `test/cstring/test.cpp` ordinary and embedded-null litmus tests for
  `memchr`, `memcmp`, `memset`, `memcpy`, and `memmove_overlap`;
- `test/cstring/proof.v` proofs for `test_memchr`,
  `test_memchr_embedded_null`, `test_memset`, `test_memcpy`, `test_memmove`,
  and `test_memcmp`.

The remaining byte-array embedded-null clients and the overlapping `memmove`
client are not yet proved.

## `<cstring>` API Surface

cppreference groups the header into:

- string manipulation: `strcpy`, `strncpy`, `strcat`, `strncat`, `strxfrm`;
- string examination: `strlen`, `strcmp`, `strncmp`, `strcoll`, `strchr`,
  `strrchr`, `strspn`, `strcspn`, `strpbrk`, `strstr`, `strtok`;
- character-array manipulation: `memchr`, `memcmp`, `memset`, `memcpy`,
  `memmove`;
- miscellaneous: `strerror`.

The implemented active slices now cover:

- `strlen`, `strcmp`, `strncmp`, `strchr`, `strrchr`, `strspn`, `strcspn`,
  `strpbrk`, `strstr`;
- `memchr`, `memcmp`, `memset`, `memcpy`, `memmove`.

## Proposed Plan

1. Done: keep the original read-only string slice stable.
   The active and archived files are meant to keep building together:
   `proof/cstring/model.vo`, `proof/cstring/pred.vo`,
   `proof/cstring/spec.vo`, `proof/cstring/model_old.vo`,
   `proof/cstring/pred_old.vo`, `proof/cstring/spec_old.vo`,
   `test/cstring/proof.vo`, and `test/cstring/proof_old.vo`.

2. Done: add explicit array-buffer litmus tests for the string slice.
   Use `char[]` examples with bytes after the first `'\0'`. In the active
   development, prove these by explicitly splitting off the `cstring.R` prefix
   and recombining the remaining buffer resource after the call.

3. Done: add read-only search and segment APIs.
   This slice covers `strchr`, `strrchr`, `strspn`, `strcspn`, `strpbrk`, and
   `strstr`. Character-search specs intentionally cover byte-range arguments
   only, matching the conservative policy in `DESIGN.md`.

4. In progress: counted byte-array APIs.
   The active specs and ordinary litmus proofs now cover `memchr`, `memcmp`,
   `memset`, `memcpy`, and non-overlapping `memmove` using abstract
   object-byte predicates. Remaining work in this slice is:
   - embedded-null regression proofs for the remaining byte-array tests;
   - overlapping `memmove`, which needs a stronger aliased or single-buffer
     spec.

5. Next: string-copy and concatenation APIs after mutable byte-array support.
   Suggested order: `strcpy`, `strncpy`, `strcat`, and `strncat`. These require
   destination capacity, mutation, null termination, and non-overlap
   preconditions.

6. Later: locale, global-state, and implementation-storage APIs.
   `strcoll`, `strxfrm`, `strerror`, and especially `strtok` involve locale,
   static/internal storage, or global tokenization state. Handle them last with
   explicit abstraction choices or narrow axiomatization.

7. Keep each slice approval-gated.
   For each slice, update `model.v` if pure semantics are needed, update
   `pred.v` only for ownership/resource predicates, add specs in `spec.v`, add
   `void` assert litmus tests in `test/cstring/test.cpp`, prove representative
   wrappers in `test/cstring/proof.v`, validate with `dune`, and then pause for
   review.
