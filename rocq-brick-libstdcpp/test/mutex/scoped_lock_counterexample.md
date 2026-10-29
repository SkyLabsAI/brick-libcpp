The current generic `scoped_lock.ctor_spec` promises both `do_lock`
continuations for a two-mutex constructor. The C++ constructor calls
`std::lock`, which may use `lock`, `try_lock`, and `unlock` in an unspecified
sequence. The `BasicLockable` and `Lockable` classes currently impose no laws
that make these operations interchangeable with respect to their effects.

`scoped_lock_counterexample.cpp` supplies a thread-safe Lockable wrapper
around `std::mutex`. Only `lock()` increments `lock_calls`; `try_lock()`
acquires the same mutex without that effect. On the supported libstdc++
implementation, the scoped constructor acquires one mutex with `lock()` and
the other with `try_lock()`. Thus the continuation `lock_calls > 0` is false
for at least one mutex, contradicting the generic contract. The executable
checks this without assuming argument order. Its expectation is specific to
libstdc++; another conforming algorithm could require a different witness.

`scoped_lock_counterexample.v` checks the contract issue independently of
the native implementation. It instantiates the existing typeclasses with
distinct flag effects, proves that the constructor's locking premises can
be supplied, checks the expansion of the actual exported constructor
contract, and proves that a false flag conflicts with its promised true
effect. This is a contract-level model: it does not verify the native mutex
implementation or prove a linked C++ program satisfies `False`. It introduces
no additional axiom or admitted lemma. The generic contract remains unfixed.

The native check runs under the Dune `runtest` alias. It can also be run with:

```
python3 scoped_lock_counterexample.py clang++ scoped_lock_counterexample.cpp
```

When fixing the contract, replace the diagnostic contract equality and
counterexample expectation with a regression that rejects the false client
claim while accepting ordinary scoped locking. A repair needs coherent
relations between locking, successful/failed try-locking, and rollback;
changing the constructor to request `do_try_lock` alone is insufficient.
