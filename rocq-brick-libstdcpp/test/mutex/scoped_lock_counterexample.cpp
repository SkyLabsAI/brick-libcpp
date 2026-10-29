// Copyright (c) 2026 SkyLabs AI, Inc.
// Distributed under the BSD 3-Clause license; see LICENSE.

#include <atomic>
#include <cstdio>
#include <mutex>

// A Lockable that distinguishes lock() from successful try_lock(). Both
// operations acquire the same underlying mutex, but only lock() increments
// lock_calls. Atomic counters preserve the Lockable's thread safety.
struct CountingMutex {
  std::mutex native;
  std::atomic<unsigned> lock_calls{0};
  std::atomic<unsigned> try_lock_calls{0};

  void lock() {
    native.lock();
    ++lock_calls;
  }

  bool try_lock() {
    ++try_lock_calls;
    return native.try_lock();
  }

  void unlock() { native.unlock(); }
};

int main() {
  CountingMutex a, b;
  {
    std::scoped_lock guard(a, b);
    const unsigned a_locks = a.lock_calls.load();
    const unsigned b_locks = b.lock_calls.load();
    const unsigned tries = a.try_lock_calls.load() + b.try_lock_calls.load();
    std::printf("lock() calls: %u, %u; try_lock() calls: %u\n",
                a_locks, b_locks, tries);

    // The current generic ctor_spec transfers both do_lock continuations.
    // Choosing the effect 'lock_calls > 0' would incorrectly promise this:
    const bool both_lock_effects = a_locks > 0 && b_locks > 0;
    std::printf("both lock() effects: %s\n", both_lock_effects ? "true" : "false");

    // This test targets the supported libstdc++ implementation. The standard
    // leaves the sequence and order unspecified; neither argument order is
    // assumed here. A different std::lock algorithm may need another witness.
    return both_lock_effects || tries == 0 ? 1 : 0;
  }
}
