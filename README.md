# brick-libcpp

Specifications of the C++ standard library in BRiCk.

## Linux pthread mutexes

`pthread.spec` also provides C function specifications for Linux/glibc's default
mutex configuration: `PTHREAD_MUTEX_NORMAL`, non-robust, process-private, with
`PTHREAD_PRIO_NONE`. These cover `pthread_mutex_init` with null attributes,
`destroy`, `lock`, `unlock`, `trylock`, `pthread_self`, and `pthread_equal`.
`pthread.mutex` reuses the mutex ghost algebras in its own invariant, without
reusing the C++ mutex function specifications.

The default lock and trylock contracts take a per-thread `not_locked`
permission. Successful acquisition returns a `locked` token and the protected
resource; unlock returns the acquisition permission. A failed trylock returns
`EBUSY` and retains the acquisition permission. Additional contracts cover a
known-held mutex, uncontended acquisition, and same-thread relocking. Relocking
a NORMAL mutex has a `False` return postcondition under partial correctness:
the call deadlocks. Destruction requires full lifetime and representation
permissions, excluding owners and outstanding calls.

`setup_initializer` and `setup_zero` consume exclusive, typed, aligned zero
storage once. They cover `PTHREAD_MUTEX_INITIALIZER` and zero-filled globals on
the supported x86-64 glibc ABI; zero-filled globals are not a portable POSIX
initialization method. `pthread_equal` compares the raw unsigned-long ID words,
including zero sentinels. This grants no mutex ownership or thread-lifetime
guarantee. The stronger `self_nonzero_spec` requires the persistent
`pthread.linux_thread_context` predicate, established at runtime entry, because
the generic logical thread-ID model permits zero. The generic `pthread_create`
contract does not yet establish this predicate for a child thread.

The usual contracts are registered by default. Select an alternative in a
local section, for example:

```coq
Definition use_owned_lock := RegisterSpec pthread.mutex.lock_owned_spec.
#[local] Existing Instance use_owned_lock.
```

The proof clients in `rocq-brick-libstdcpp/test/pthread/mutex*.v` demonstrate
the alternatives and initialization rules; `owner.v` covers owner tracking and
re-entry by the existing owner. Native tests check the corresponding glibc
behavior. Owner-tracking helpers still need their own invariant and race
freedom proof; comparing an owner word cannot replace an ownership token.

## Development

To develop on these specifications, you'll need clang, the GNU C++ library (not
clang's own version), and Skylabs AI's verification toolchain.

If you have access to our automation sources, you can check this out as part of
https://github.com/SkyLabsAI/workspace. After `make vendored-pull fmdeps-pull`,
you'll find a copy of this repository in `fmdeps/brick-libcpp`. Build from the
composed workspace root:

```sh
dune build fmdeps/brick-libcpp
```

For Docker-backed builds, see the
[BRiCk Docker setup documentation](https://github.com/SkyLabsAI/BRiCk/blob/main/rocq-skylabs-cpp2v/scripts/README.md).
