# Conditional finding: a transferable `pthread.handle` makes `pthread_join` unsound

> Written by Claude (Claude Code).

`pthread_join` requires `pthread.handle γ this_thread tid P` and promises to return 0.
The `spawner` argument of the handle is meant to rule out two threads joining each
other (SkyLabsAI/brick-libcpp#262). But `thread_idT` is the raw `pthread_t` value,
and C libraries reuse those once a thread is joined. A thread whose id is the reused
id of a handle's spawner passes the check without being that thread.

On `main` this cannot be exploited, because no handle can leave the thread that
created it (see "Missing step"). This finding shows what goes wrong as soon as one
can, for example to fix SkyLabsAI/brick-libcpp#259.

## 1. Principle

```rocq
Hypothesis handle_local : ∀ γ spawner tid (P : mpred),
  LocalWith procTI P → LocalWith procTI (pthread.handle γ spawner tid P).
```

## 2. Why it is defensible

- SkyLabsAI/brick-libcpp#259 asks for exactly this: letting a thread other than the
  creator join. The joiner can only get the handle if it can cross threads, and
  `pthread_create` passes resources across threads only when `Pre` and `Post` are
  `LocalWith procTI`.
- A handle is ghost state plus two ids, none of it thread-local. The memory
  predicates it would travel with already have this instance
  (`tptsto_pd_local_weakly_obj`, `has_type_pd_weakly_obj`, ... in
  `proof/runtime/objective.v`).
- The hypothesis is the weak, conditional form: it only applies when the payload
  `P` is itself `LocalWith procTI`, which `pthread_create` already requires.

## 3. Derivation

`test/pthread/join_reuse_cycle_proof.v`, `test_never_returns`: under
`handle_local`,

```
denoteModule source ∗ create_spec ∗ join_spec ∗ (std::thread::id specs) ⊢ test_spec
```

where `test_spec` is `\post False` for `test()` in `join_reuse_cycle.cpp`:

1. `test()` starts S, and S records its id `th_S` and creates X. S returns its
   handle for X (spawner `th_S`) through its `Post`, which needs `handle_local`.
2. `test()` joins S and publishes the handle in a process-local invariant on
   `Shared::st`. X takes it, starts Y, and passes it to Y through Y's `Pre`
   (`handle_local` again).
3. Y compares `std::this_thread::get_id()` with `th_S`. In the equal branch,
   `current_thread th_S` holds, so `pthread_join(X)` meets `join_spec`. Meanwhile X
   joins Y with its own handle.
4. `join_spec` says both joins return 0, so the calls to `set_failed` after a failed
   join are dead code. The invariant then keeps `Shared::failed` at 0, and
   `test()`'s final `while (!load_failed(&sh))` never exits.

The logic never sees the cycle; it only needs Y's id check to succeed. At run time,
the check succeeds whenever Y reuses S's `pthread_t`, which glibc does once S is
joined.

`Print Assumptions test_never_returns` lists only `Corelib.`, `skylabs.` and four
standard `Stdlib` axioms (`classic`, `functional_extensionality_dep`,
`ClassicalDedekindReals.sig_forall_dec` / `sig_not_dec`). Notes on the `skylabs.`
entries:

- The proof does not use auto's `UNSOUND_eval_nd`, `UNSOUND_eval_l_nd` or
  `UNSOUND_nd_seq`. It removes those hints, along with the hints whose proofs
  use them (`wp_operand_binop_wp`, used for `==` and `!=`, and both
  `wp_lval_assign` hints). It splits every nondeterministic evaluation order
  explicitly (`gond`). This is why the C++ uses `!`, int-to-bool tests and default
  member initializers rather than built-in comparisons and assignments.
- It does not import `proof/pthread/hints.v`, whose obligations are admitted.
  `starter_specR` is unlocked directly instead.
- It still uses `skylabs.auto.cpp.hints.wp.wp_f2p_gvar`, an `Admitted` lemma in
  auto that every direct function call goes through. It concerns the alignment of
  function pointers, and it is not involved in the cycle.

## 4. Missing step

Any instance that lets a `pthread.handle` leave its creating thread:
`LocalWith procTI` (through `pthread_create`'s `Pre`/`Post`), or `WeaklyObjective`
(through invariants or locks), while all of the following still hold:

- `join_spec` uses `spawner = this_thread` as its only guard against cycles;
- `join_spec` promises `\post[Vint 0]`;
- `thread_idT` stays the raw, reusable `pthread_t` value.

Today the guard is unnecessary: joiner = creator, so the join graph is a subgraph
of the spawn tree, and the spawn tree is acyclic. That is a consequence of the
missing instance, not of `spawner`.

## 5. Blast radius

Once a handle can move, `pthread_join`'s `\post[Vint 0]` holds only on C libraries
that never report `EDEADLK` for a cycle. POSIX allows `EDEADLK` for any detected
deadlock. Every client that ignores `pthread_join`'s result could then derive
results that a conforming implementation refutes. Any fix of SkyLabsAI/brick-libcpp#259 must
come with a real acyclicity argument (ranks or levels on handles, or a ghost
identity that is not reused), or report `EDEADLK` in the postcondition.

## Run-time evidence

The program runs under glibc 2.41 (`ghcr.io/skylabsai/workspace:fm-default`) with
clang 22, built with the same flags that `cpp2v` uses (`-std=c++20 -stdlib=libstdc++`):

| C library behaviour | `-O0` | `-O2` |
|---|---|---|
| plain glibc (no cycle detection) | hangs (timeout) | hangs (timeout) |
| `LD_PRELOAD=join_detect_cycle.so` | exit 0 + `REACHED_END_OF_TEST`, 5/5 | exit 0 + `REACHED_END_OF_TEST`, 5/5 |

`join_detect_cycle.c` is a `pthread_join` that reports `EDEADLK` for self-joins and
for two threads joining each other, then defers to glibc. That is a behaviour POSIX
permits. Plain glibc hanging is consistent with the specs (partial correctness), so
this is not a gate pass on glibc. It is one under any POSIX implementation that
detects the cycle, provided the missing step lands.

```sh
gcc -shared -fPIC join_detect_cycle.c -o det.so -ldl
clang++ -std=c++20 -stdlib=libstdc++ -O2 join_reuse_cycle.cpp -o w
LD_PRELOAD=./det.so timeout 10 ./w; echo exit=$?
```
