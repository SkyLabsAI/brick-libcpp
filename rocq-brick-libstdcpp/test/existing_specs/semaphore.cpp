#include <cassert>
#include <semaphore>

using semaphore_one = std::counting_semaphore<1>;

void test_construct_zero_destroy() {
  semaphore_one semaphore(0);
}

void test_permit_cycle_without_query() {
  semaphore_one semaphore(1);

  semaphore.acquire();
  semaphore.release(1);
}

void test_zero_release_boundary_without_query() {
  semaphore_one semaphore(1);

  semaphore.release(0);
  semaphore.acquire();
  semaphore.release(1);
}

void test_zero_permit_try_acquire() {
  semaphore_one semaphore(0);

  // With no permit, try_acquire cannot perform its decrement and must fail.
  assert(!semaphore.try_acquire());
}

void test_acquire_release_cycle() {
  semaphore_one semaphore(1);

  // The initial permit avoids relying on another thread to release one.
  semaphore.acquire();
  assert(!semaphore.try_acquire());

  semaphore.release(1);
  semaphore.acquire();
  semaphore.release(1);
}

void test_available_permit_allows_spurious_failure() {
  semaphore_one semaphore(1);

  // The standard permits a spurious false result even while a permit exists.
  // Restore the permit only when the call actually consumed it.
  const bool acquired = semaphore.try_acquire();
  if (acquired) {
    semaphore.release(1);
  }

  // Both branches leave one permit, so no cross-thread release is needed.
  semaphore.acquire();
  semaphore.release(1);
}

void test_zero_release_is_noop() {
  semaphore_one semaphore(1);

  // update == 0 is the lower valid boundary for release.
  semaphore.release(0);
  semaphore.acquire();
  assert(!semaphore.try_acquire());
  semaphore.release(1);
}

// This function is proof-only negative evidence and must never be executed:
// desired > max() violates the counting_semaphore constructor precondition.
void misuse_initial_count_above_max() {
  semaphore_one semaphore(2);
}

int main() {
  test_construct_zero_destroy();
  test_permit_cycle_without_query();
  test_zero_release_boundary_without_query();
  test_zero_permit_try_acquire();
  test_acquire_release_cycle();
  test_available_permit_allows_spurious_failure();
  test_zero_release_is_noop();
}
