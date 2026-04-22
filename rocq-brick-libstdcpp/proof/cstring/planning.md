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

The current workspace contains coherent first and second slices for read-only
null-terminated byte-string operations:

- `model.v` defines pure byte-string models for `strcmp`, `strncmp`, `strchr`,
  `strrchr`, `strspn`, `strcspn`, `strpbrk`, and `strstr`; the active `strlen`
  spec uses the existing `cstring.strlen`.
- `pred.v` is intentionally minimal and reuses the existing `cstring.R`
  abstraction.
- `spec.v` specifies `strlen`, `strcmp`, `strncmp`, `strchr`, `strrchr`,
  `strspn`, `strcspn`, `strpbrk`, and `strstr` against `cstring.R`.
- `test/cstring/test.cpp` contains `void` litmus functions using `assert`.
  The embedded-null literal cases are isolated into separate functions from the
  ordinary `strlen`, `strcmp`, and `strncmp` tests; the search/segment slice
  includes ordinary tests and an embedded-null `char[]` array-buffer client.
- `test/cstring/proof.v` proves the ordinary `strlen`, `strcmp`, `strncmp`,
  search/segment tests, array-buffer client tests, and slice-wrapper tests.
  The embedded-null literal tests are specified there but left admitted because
  active clients must first split larger literal resources before invoking the
  `cstring.R` specs.
- `test/cstring/proof_old.v` proves the same ordinary tests and also proves the
  embedded-null tests using the archived lower-level bridge.
- `DESIGN.md` records the representation choice and remaining design notes.

The main abstraction boundary is that `cstring.R` remains the convenient
client-facing null-terminated string predicate. The older `cstringz.R` predicate
is preserved only in `pred_old.v` and used by `proof_old.v` to demonstrate how
embedded-null literal resources can be split and recombined around calls to the
active specs.

## `<cstring>` API Surface

cppreference groups the header into:

- string manipulation: `strcpy`, `strncpy`, `strcat`, `strncat`, `strxfrm`;
- string examination: `strlen`, `strcmp`, `strncmp`, `strcoll`, `strchr`,
  `strrchr`, `strspn`, `strcspn`, `strpbrk`, `strstr`, `strtok`;
- character-array manipulation: `memchr`, `memcmp`, `memset`, `memcpy`,
  `memmove`;
- miscellaneous: `strerror`.

The implemented read-only slices cover `strlen`, `strcmp`, `strncmp`, `strchr`,
`strrchr`, `strspn`, `strcspn`, `strpbrk`, and `strstr`.

## Proposed Plan

1. Done: keep the existing v1 slice stable.
   The active and archived files currently validate with `dune`; keep checking
   them when touching this area:
   `proof/cstring/model.vo`, `proof/cstring/pred.vo`,
   `proof/cstring/spec.vo`, `proof/cstring/model_old.vo`,
   `proof/cstring/pred_old.vo`, `proof/cstring/spec_old.vo`,
   `test/cstring/proof.vo`, and `test/cstring/proof_old.vo`.

2. Done: add explicit array-buffer litmus tests for the v1 slice.
   Use `char[]` examples with bytes after the first `'\0'`. In the active
   development, prove these by explicitly splitting off the `cstring.R` prefix
   and recombining the remaining buffer resource after the call. Keep tests as
   `void` functions with `assert`. The active `test/cstring/proof.v` now has
   these proofs; extending `test/cstring/proof_old.v` with matching archived
   proofs is an optional leftover task, not part of this completed step.

3. Done: add read-only search and segment APIs.
   This slice covers `strchr`, `strrchr`, `strspn`, `strcspn`, `strpbrk`, and
   `strstr`. The active development has pure models, `cstring.R`-based specs,
   ordinary litmus tests, and an embedded-null `char[]` array-buffer client
   proof. Character-search specs intentionally cover byte-range arguments only,
   matching the conservative policy in `DESIGN.md`.

4. Add byte-array APIs as a separate slice.
   Suggested order: `memcmp`, `memchr`, then `memset`, then `memcpy`, then
   `memmove`. These operate over counted arrays and do not require null
   termination, so they likely need a distinct byte-buffer predicate/model.

5. Add string-copy and concatenation APIs after mutable byte-array support.
   Suggested order: `strcpy`, `strncpy`, `strcat`, and `strncat`. These require
   destination capacity, mutation, null termination, and non-overlap
   preconditions.

6. Defer locale, global-state, and implementation-storage APIs.
   `strcoll`, `strxfrm`, `strerror`, and especially `strtok` involve locale,
   static/internal storage, or global tokenization state. Handle them last with
   explicit abstraction choices or narrow axiomatization.

7. Keep each slice approval-gated.
   For each slice, update `model.v` if pure semantics are needed, update
   `pred.v` only for ownership/resource predicates, add specs in `spec.v`, add
   `void` assert litmus tests in `test/cstring/test.cpp`, prove representative
   wrappers in `test/cstring/proof.v`, validate with `dune`, and then pause for
   review.
