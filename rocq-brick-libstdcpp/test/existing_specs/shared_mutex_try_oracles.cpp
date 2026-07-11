#include <cassert>
#include <shared_mutex>

// Phase B selects the direct alternative try_lock/unlock registrations here.
int try_exclusive_alt_oracle() {
  std::shared_mutex mutex;
  int protected_value = 80;

  bool acquired = mutex.try_lock();
  if (acquired) {
    protected_value += 1;
    mutex.unlock();
  }

  mutex.lock_shared();
  int result = protected_value;
  mutex.unlock_shared();
  return result;
}

// Phase B selects the canonical try_lock/unlock registrations here.
int try_exclusive_canonical_oracle() {
  std::shared_mutex mutex;
  int protected_value = 90;

  bool acquired = mutex.try_lock();
  if (acquired) {
    protected_value += 1;
    mutex.unlock();
  }

  mutex.lock_shared();
  int result = protected_value;
  mutex.unlock_shared();
  return result;
}

int try_shared_oracle() {
  std::shared_mutex mutex;
  int protected_value = 100;

  bool acquired = mutex.try_lock_shared();
  int result = -1;
  if (acquired) {
    result = protected_value;
    mutex.unlock_shared();
  }

  // Both failure-with-no-effect and released success permit this acquisition.
  mutex.lock();
  protected_value += 1;
  mutex.unlock();

  return result;
}

int main() {
  int exclusive_alt = try_exclusive_alt_oracle();
  assert(exclusive_alt == 80 || exclusive_alt == 81);

  int exclusive_canonical = try_exclusive_canonical_oracle();
  assert(exclusive_canonical == 90 || exclusive_canonical == 91);

  int shared = try_shared_oracle();
  assert(shared == -1 || shared == 100);

  return 0;
}
