#include <cassert>
#include <shared_mutex>

struct TryObservation {
  bool acquired;
  int branch_value;
  int post_cleanup_value;
};

int lifecycle_scope() {
  int marker = 16;
  {
    std::shared_mutex mutex;
    (void)mutex;
    marker += 1;
  }
  return marker;
}

// Phase B should select lock_spec_alt and unlock_spec_alt for this client.
int exclusive_alt_cycle() {
  std::shared_mutex mutex;
  int protected_value = 40;

  mutex.lock();
  protected_value += 2;
  mutex.unlock();

  return protected_value;
}

// Phase B should select the canonical lock_spec and unlock_spec registrations.
int exclusive_canonical_cycle() {
  std::shared_mutex mutex;
  int protected_value = 50;

  mutex.lock();
  protected_value += 2;
  mutex.unlock();

  return protected_value;
}

int shared_cycle() {
  std::shared_mutex mutex;
  int protected_value = 60;

  mutex.lock_shared();
  int observed = protected_value;
  mutex.unlock_shared();

  return observed;
}

int exclusive_then_shared_cycle() {
  std::shared_mutex mutex;
  int protected_value = 70;

  mutex.lock();
  protected_value += 1;
  mutex.unlock();

  mutex.lock_shared();
  int observed = protected_value;
  mutex.unlock_shared();

  return observed;
}

// Phase B should select try_lock_spec_alt and unlock_spec_alt on success.
TryObservation try_exclusive_alt_cycle() {
  std::shared_mutex mutex;
  int protected_value = 80;

  bool acquired = mutex.try_lock();
  if (acquired) {
    protected_value += 1;
    mutex.unlock();
  }

  // A failed try_lock has no effects.  On success, unlock restores the same
  // legal state, so either path permits this deterministic shared acquisition.
  mutex.lock_shared();
  int post_cleanup_value = protected_value;
  mutex.unlock_shared();

  return {acquired, protected_value, post_cleanup_value};
}

// Phase B should select canonical try_lock_spec and unlock_spec on success.
TryObservation try_exclusive_canonical_cycle() {
  std::shared_mutex mutex;
  int protected_value = 90;

  bool acquired = mutex.try_lock();
  if (acquired) {
    protected_value += 1;
    mutex.unlock();
  }

  mutex.lock_shared();
  int post_cleanup_value = protected_value;
  mutex.unlock_shared();

  return {acquired, protected_value, post_cleanup_value};
}

TryObservation try_shared_cycle() {
  std::shared_mutex mutex;
  int protected_value = 100;

  bool acquired = mutex.try_lock_shared();
  int branch_value = -1;
  if (acquired) {
    branch_value = protected_value;
    mutex.unlock_shared();
  }

  // Both the no-effect failure path and the released success path permit a
  // later exclusive acquisition.
  mutex.lock();
  protected_value += 1;
  int post_cleanup_value = protected_value;
  mutex.unlock();

  return {acquired, branch_value, post_cleanup_value};
}

int main() {
  assert(lifecycle_scope() == 17);
  assert(exclusive_alt_cycle() == 42);
  assert(exclusive_canonical_cycle() == 52);
  assert(shared_cycle() == 60);
  assert(exclusive_then_shared_cycle() == 71);

  TryObservation exclusive_alt = try_exclusive_alt_cycle();
  if (exclusive_alt.acquired) {
    assert(exclusive_alt.branch_value == 81);
  } else {
    assert(exclusive_alt.branch_value == 80);
  }
  assert(exclusive_alt.post_cleanup_value == exclusive_alt.branch_value);

  TryObservation exclusive_canonical = try_exclusive_canonical_cycle();
  if (exclusive_canonical.acquired) {
    assert(exclusive_canonical.branch_value == 91);
  } else {
    assert(exclusive_canonical.branch_value == 90);
  }
  assert(exclusive_canonical.post_cleanup_value ==
         exclusive_canonical.branch_value);

  TryObservation shared = try_shared_cycle();
  if (shared.acquired) {
    assert(shared.branch_value == 100);
  } else {
    assert(shared.branch_value == -1);
  }
  assert(shared.post_cleanup_value == 101);

  return 0;
}
