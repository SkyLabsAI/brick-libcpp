# `<ctime>` BRiCk Spec Design

## 1. Summary

1. Add a new `proof/ctime` folder and a companion `test/ctime` folder.
2. Cover the standard `<ctime>` surface from cppreference and C11 7.27, with `difftime` deferred because BRiCk does not currently support doubles.
3. Use an abstract-but-accurate design: explicit ownership for writable outputs, borrowed resources for static return objects, and abstract model relations for time conversion and formatting.

## 2. Public API and Representation Changes

1. The proof folder contains `inc_ctime.cpp`, `pred.v`, `model.v`, and `spec.v`.
2. Specs target the unqualified names emitted by `cpp2v`: `clock`, `time`, `mktime`, `gmtime`, `localtime`, `asctime`, `ctime`, `strftime`, and `timespec_get`.
3. V1 remains standard-only and excludes glibc and POSIX extensions visible in the generated AST.
4. The model layer exports `tm_model` and `timespec_model`.
5. `tmR` hides non-standard `tm_gmtoff` and `tm_zone` fields behind `tmR_hidden`, while `timespecR` tracks only `tv_sec` and `tv_nsec`.

## 3. Specification Design

1. `clock` and `time` are modeled as abstract current-time queries over signed integer results.
2. `timespec_get` is only specified for `TIME_UTC = 1`.
3. `mktime`, `gmtime`, and `localtime` use abstract conversion and normalization relations instead of a concrete calendar algorithm.
4. `asctime` and `ctime` return borrowed C strings with explicit close obligations, matching the existing static-storage style used elsewhere in the repo.
5. `strftime` writes into a caller-owned `cstring.bufR` buffer and returns either `0` or the produced string length.

## 4. Validation Plan

1. `test/ctime/test.cpp` exercises `std::time`, `std::timespec_get`, `std::mktime`, `std::gmtime`, `std::localtime`, `std::asctime`, `std::ctime`, `std::strftime`, and repeated static-return calls.
2. `test/ctime/proof.v` proves representative client lemmas against the new specs.
3. The test clients use `std::`-qualified calls so the proof confirms those names resolve against the unqualified spec entries produced by `cpp2v`.

## 5. Known Deviation

1. `difftime` is intentionally deferred until BRiCk has a supported story for `double` values in specs and proofs.
