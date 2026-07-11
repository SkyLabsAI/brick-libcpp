#include <cassert>
#include <mutex>
#include <new>

using RecursiveMutex = std::recursive_mutex;

// Dedicated Phase-B selection site for the base constructor/destructor pair.
bool unlocked_lifecycle_oracle() {
  RecursiveMutex* mutex = nullptr;
  while (mutex == nullptr) {
    mutex = new (std::nothrow) RecursiveMutex;
  }
  delete mutex;

  return true;
}

// Dedicated Phase-B selection site for base lock_spec/unlock_spec.
bool base_recursive_protocol_oracle() {
  RecursiveMutex mutex;
  int protected_value = 0;

  mutex.lock();
  protected_value = 1;
  mutex.lock();
  protected_value += 2;
  mutex.unlock();
  protected_value += 4;
  mutex.unlock();

  mutex.lock();
  const int snapshot = protected_value;
  mutex.unlock();
  return snapshot == 7;
}

// Dedicated Phase-B selection site for ctor_spec', lock_spec', and
// unlock_spec'.
bool derived_recursive_protocol_oracle() {
  int protected_value = 5;
  RecursiveMutex mutex;

  mutex.lock();
  protected_value *= 2;
  mutex.lock();
  protected_value += 3;
  mutex.unlock();
  protected_value += 7;
  const int snapshot = protected_value;
  mutex.unlock();

  mutex.lock();
  mutex.unlock();
  return snapshot == 20;
}

// Same C++ lock/unlock symbols, kept separate for Phase-B selection of the
// BasicLockable-derived lock_spec_alt'/unlock_spec_alt' keys.
bool basic_lockable_alternative_oracle() {
  int protected_value = 3;
  RecursiveMutex mutex;

  mutex.lock();
  protected_value += 4;
  mutex.lock();
  protected_value *= 3;
  mutex.unlock();
  protected_value -= 1;
  const int snapshot = protected_value;
  mutex.unlock();

  mutex.lock();
  mutex.unlock();
  return snapshot == 20;
}

int main() {
  assert(unlocked_lifecycle_oracle());
  assert(base_recursive_protocol_oracle());
  assert(derived_recursive_protocol_oracle());
  assert(basic_lockable_alternative_oracle());
  return 0;
}
