#include <cassert>
#include <mutex>

using mutex_type = std::mutex;
using guard_type = std::lock_guard<mutex_type>;

int lock_guard_scope_round_trip() {
  mutex_type mutex;
  int protected_value = 41;

  {
    guard_type guard(mutex);
    ++protected_value;
    assert(protected_value == 42);
  }

  assert(protected_value == 42);
  return protected_value;
}

int lock_guard_reacquire_after_scope() {
  mutex_type mutex;
  int protected_value = 5;

  {
    guard_type first_guard(mutex);
    protected_value = 7;
  }

  {
    guard_type second_guard(mutex);
    assert(protected_value == 7);
    protected_value = 9;
  }

  assert(protected_value == 9);
  return protected_value;
}

int lock_guard_function_scope_cleanup() {
  mutex_type mutex;
  int protected_value = 10;
  guard_type guard(mutex);

  ++protected_value;
  assert(protected_value == 11);
  return protected_value;
}

int main() {
  assert(lock_guard_scope_round_trip() == 42);
  assert(lock_guard_reacquire_after_scope() == 9);
  assert(lock_guard_function_scope_cleanup() == 11);
  return 0;
}
