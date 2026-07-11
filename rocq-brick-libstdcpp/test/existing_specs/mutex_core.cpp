#include <cassert>
#include <mutex>

void mutex_construct_destroy() {
  {
    std::mutex mutex;
    (void)mutex;
  }
}

int mutex_direct_lock_unlock() {
  std::mutex mutex;
  int protected_value = 0;

  mutex.lock();
  protected_value = 1;
  mutex.unlock();

  assert(protected_value == 1);
  return protected_value;
}

int mutex_basic_lockable_lock_unlock() {
  std::mutex mutex;
  int protected_value = 0;

  mutex.lock();
  protected_value = 2;
  mutex.unlock();

  assert(protected_value == 2);
  return protected_value;
}

bool mutex_direct_try_lock() {
  std::mutex mutex;
  int protected_value = 0;

  const bool acquired = mutex.try_lock();
  if (acquired) {
    protected_value = 1;
    mutex.unlock();
  }

  assert(protected_value == (acquired ? 1 : 0));
  return acquired;
}

bool mutex_lockable_try_lock() {
  std::mutex mutex;
  int protected_value = 0;

  const bool acquired = mutex.try_lock();
  if (acquired) {
    protected_value = 2;
    mutex.unlock();
  }

  assert(protected_value == (acquired ? 2 : 0));
  return acquired;
}

int mutex_realistic_composition() {
  std::mutex mutex;
  int protected_value = 0;

  mutex.lock();
  protected_value = 1;
  mutex.unlock();

  const bool acquired = mutex.try_lock();
  if (acquired) {
    ++protected_value;
    mutex.unlock();
  }

  assert(protected_value == (acquired ? 2 : 1));
  return protected_value;
}

int main() {
  mutex_construct_destroy();
  assert(mutex_direct_lock_unlock() == 1);
  assert(mutex_basic_lockable_lock_unlock() == 2);
  (void)mutex_direct_try_lock();
  (void)mutex_lockable_try_lock();

  const int composed = mutex_realistic_composition();
  assert(composed == 1 || composed == 2);
  return 0;
}
