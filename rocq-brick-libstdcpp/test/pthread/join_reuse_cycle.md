# Join cycles through reused thread ids

> Written by Claude (Claude Code).

Regression test for SkyLabsAI/brick-libcpp#262.

## The problem

`pthread_join` used to require `pthread.handle γ this_thread tid P`, where
`this_thread` was the handle's *spawner*, the thread that created `tid`. It
promised to return 0. The spawner check was meant to rule out two threads joining
each other. But `thread_idT` is the raw `pthread_t` value, and C libraries reuse
those once a thread is joined. A thread whose id is the reused id of a handle's
spawner passed the check without being that thread.

On its own this could not be exploited: no handle could leave the thread that
created it, so the joiner was always the creator. The join graph was a subgraph of
the acyclic spawn tree. Any instance letting a handle move would have broken that,
for example `LocalWith procTI` through `pthread_create`'s `Pre`/`Post`, which
SkyLabsAI/brick-libcpp#259 needs. With the hypothesis

```rocq
Hypothesis handle_local : ∀ γ spawner tid (P : mpred),
  LocalWith procTI P → LocalWith procTI (pthread.handle γ spawner tid P).
```

the original `join_reuse_cycle.cpp` verified against `\post False` (commit
"test(pthread): conditional finding, transferable handles make join unsound"):

1. `test()` starts S, and S records its id `th_S` and creates X. S returns its
   handle for X (spawner `th_S`) through its `Post`.
2. `test()` joins S and publishes the handle in a process-local invariant on
   `Shared::st`. X takes it, starts Y, and passes it to Y through Y's `Pre`.
3. Y compares `std::this_thread::get_id()` with `th_S`. In the equal branch,
   `current_thread th_S` holds, so `pthread_join(X)` met `join_spec`. Meanwhile X
   joins Y with its own handle.
4. `join_spec` said both joins return 0, so the calls to `set_failed` after a
   failed join were dead code. `Shared::failed` stayed 0, and `test()`'s final
   `while (!load_failed(&sh))` never exited.

Yet the program returns under a `pthread_join` that reports the cycle with
`EDEADLK`, which POSIX allows (see "Run-time evidence").

## The fix

- `pthread.handle γ tid P` no longer records a spawner, and neither
  `pthread_create` nor `pthread_join` mentions the current thread.
- `pthread_join` returns `err`. If `err = 0`, it gives back `P`. Otherwise, the
  error is `EDEADLK`: the joined thread may still be running and owns `P`, so the
  handle is lost.

Clients must now handle a failed join. If the joined thread uses the caller's
locals, the caller cannot return; `multithreaded_ok` in `test.cpp` calls `abort()`.

## The regression test

`join_reuse_cycle_proof.v` uses the `pthread.handle_local_with` instance, the same
principle as `handle_local` without the spawner, and verifies the same threads. Every failed join is now a reachable path that sets
`Shared::failed`, so `test()` verifies against `\post emp` (`test_from_specs`).
The program changed in three places, so that it can meet that postcondition:

- `test()` takes `Shared*` from a static in `main`, because the threads may still
  use it after `test()` returns;
- `test()` publishes S's handle for X only if joining S succeeded;
- `s_fn` aborts if creating X fails, since it then has no handle to return.

Against the new specs, the original `\post False` proof, changed only for the
handle's new arity, fails in `y_ok`. The open goals are the branch where
`pthread_join` returned nonzero and calls `set_failed`, whose spec required
`False`.

`handle_local` was a section hypothesis at first. SkyLabsAI/brick-libcpp#259 added
it to the library as the `pthread.handle_local_with` instance, which the proof now
uses.

The original proof used to not depend on auto's `UNSOUND_eval_nd`,
`UNSOUND_eval_l_nd` or `UNSOUND_nd_seq`. It removed those hints, along with the
hints whose proofs use them (`wp_operand_binop_wp`, used for `==` and `!=`, and
both `wp_lval_assign` hints). It split every nondeterministic evaluation order
explicitly (`gond`). This is why the C++ code uses `!`, int-to-bool tests and
default member initializers rather than built-in comparisons and assignments.
These oddities in the C++ code remain but the proof no longer avoids the unsound
axioms.

## Run-time evidence

The program runs under glibc 2.41 (`ghcr.io/skylabsai/workspace:fm-default`) with
clang 22, built with the same flags that `cpp2v` uses (`-std=c++20 -stdlib=libstdc++`):

| C library behaviour | `-O0` | `-O2` |
|---|---|---|
| plain glibc (no cycle detection) | hangs (timeout) | hangs (timeout) |
| `LD_PRELOAD=join_detect_cycle.so` | exit 0 + `REACHED_END_OF_TEST`, 5/5 | exit 0 + `REACHED_END_OF_TEST`, 5/5 |

`join_detect_cycle.c` is a `pthread_join` that reports `EDEADLK` for self-joins and
for two threads joining each other, then defers to glibc. That is a behaviour POSIX
permits. Both the original and the current program behave this way.

```sh
gcc -shared -fPIC join_detect_cycle.c -o det.so -ldl
clang++ -std=c++20 -stdlib=libstdc++ -O2 join_reuse_cycle.cpp -o w
LD_PRELOAD=./det.so timeout 10 ./w; echo exit=$?
```
