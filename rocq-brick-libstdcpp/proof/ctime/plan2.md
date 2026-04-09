# `<ctime>` Refactor And Proof-Repair Plan

## Summary

1. Keep both client styles in `test/ctime`: green wrapper clients for normal validation and stack-local POD repro clients for the `tm::~tm()` / `timespec::~timespec()` verifier completeness bug.
2. Refactor the `ctime` proof stack so `model.v` is pure-only and `pred.v` owns all separation predicates, including `later_than`, `tmR`, and `timespecR`.
3. Rework `tmR` with `sl.lock` and `#[only(lazy_unfold)] derive` so it stays abstract in client proofs while hiding non-standard `tm` fields.
4. Repair as many non-repro proofs as possible, using `dune coq top` / `dune rocq top` for live replay, while keeping the POD repro lemmas explicit and buildable.

## Key Changes

1. Refactor the layer split.
   `model.v` will contain only pure definitions and `Prop`-valued relations.
   Move `tm_model` and `timespec_model` into `model.v`.
   Keep `TIME_UTC`, `clock_t_model`, `time_t_model`, `clock_result`, `timespec_get_result`, `utc_time_to_tm`, `local_time_to_tm`, `mktime_result`, `asctime_text_of`, `strftime_text_of`, and `ctime_text_of` in `model.v`.
   `pred.v` will import `model.v` and define all `Rep` / `mpred`-valued abstractions.

2. Replace `current_time_result` with `later_than` in `pred.v`.
   Remove `current_time_result` entirely.
   Define `later_than` as a `Parameter`, not by copy-pasting the class-based NOVA code.
   Add the needed supporting declarations in parameter/axiom form: `Knowledge1 later_than`, `Timeless1 later_than`, `WeaklyObjective1 later_than`, and the down-closed law.
   Do not add `Hint Opaque later_than` or `Arguments later_than : simpl never.`, since `later_than` is a parameter and those lines would add no value.
   Update the `time` spec so success returns the integer time value and `later_than` for that value, and `time(&t)` also writes the same integer to `*t`.

3. Rework `tmR` to match the intended public contract.
   Publicly expose only the 9 ISO C `tm` fields via `tm_model`.
   Keep `tm_gmtoff` and `tm_zone` hidden inside `tmR_hidden`.
   Do not decide now whether `tm_zone` is owned, borrowed, or ignored; hide that choice inside `tmR_hidden` and add a TODO comment for later investigation.
   Implement the exported `tmR` through a locked wrapper.
   Prefer `sl.lock` and `#[only(lazy_unfold)] derive` to solve the current transparency issue instead of ad hoc opacity hints.
   Apply the same style to any other exported rep that needs abstraction control in client proofs.

4. Keep `timespecR` simple and standard-facing.
   `timespecR` continues to describe only `tv_sec` and `tv_nsec`.
   If abstraction control is needed for `timespecR`, use the same locked/lazy-unfold pattern as `tmR`.

5. Update the client suite to include both green and repro paths.
   Add pointer-wrapper clients for `timespec_get` and `mktime` so those APIs have green proof-backed coverage without local POD cleanup.
   Keep stack-local POD repro clients for both `std::timespec` and `std::tm`.
   Keep direct green clients for `gmtime`, `localtime`, `asctime`, `ctime`, `strftime`, and repeated static-return calls, unless proof replay shows a strictly better shape.
   Keep `main()` on the green path only so `main_ok` remains part of the normal successful build.

6. Update `test/ctime/proof.v` to reflect the split.
   Fully prove the green clients where feasible.
   Keep the POD repro lemmas under `verify?` and explicitly `Admitted` if the destructor-spec bug still blocks them.
   Add short comments stating that those lemmas intentionally preserve a verifier completeness repro.
   For non-repro lemmas, do not stop at the first failure: try to repair each proof, or leave the most-progress script if full discharge is still blocked.

## Proof Repair Strategy

1. First fix the representation-level blocker.
   Refactor `tmR` and `timespecR` so client proofs no longer fail on transparent rep expansion.

2. Then replay each non-repro client proof individually.
   Use `dune coq top` or `dune rocq top` from the `rocq-brick-libstdcpp` project root as the default live environment.
   Prefer dune-managed tops over plain `coqtop` for proof inspection and debugging.
   Keep proof edits local and minimal; do not introduce broad infrastructure unless repeated failures show it is necessary.

3. Treat the POD destructor repros separately.
   Preserve isolated repro lemmas for local `tm` and local `timespec`.
   Keep them buildable through explicit admissions if the verifier still insists on destructor specs without bodies.

## Validation Plan

1. Rebuild `./test/ctime/proof.vo` as the main acceptance target.
2. Confirm the green path proves successfully, including `main()`.
3. Confirm the POD repro lemmas remain present and documented.
4. Confirm the generated `test_cpp.v` still contains local `tm` and `timespec` objects for the repro cases.
5. Re-run proof replay on every non-repro lemma and retain the strongest checked script reached for each one.

## Assumptions And Defaults

1. The final `ctime` test theory should stay buildable even if POD repro lemmas remain admitted.
2. `later_than` is a local `ctime` abstraction in `pred.v`, not an import of NOVA’s shared predicate framework.
3. The `tm_zone` ownership question is intentionally deferred and hidden inside `tmR_hidden`.
4. `difftime` remains deferred.
