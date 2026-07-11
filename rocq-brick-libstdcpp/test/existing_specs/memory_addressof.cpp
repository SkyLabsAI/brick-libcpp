#include <cassert>
#include <memory>

struct overloaded_address {
  int value;

  // addressof must bypass this user-defined address operation.
  overloaded_address* operator&() noexcept { return nullptr; }
  const overloaded_address* operator&() const noexcept { return nullptr; }
};

void test_public_addressof_int() {
  int value = 7;
  int* pointer = std::addressof(value);

  assert(pointer == &value);
  *pointer = 11;
  assert(value == 11);
}

void test_public_addressof_overloaded() {
  overloaded_address object{17};
  overloaded_address* pointer = std::addressof(object);

  assert(pointer != nullptr);
  assert(pointer->value == 17);
  pointer->value = 19;
  assert(object.value == 19);
}

void test_internal_addressof_int() {
  // Nonportable libstdc++ implementation-helper probe.
  int value = 23;
  int* pointer = std::__addressof(value);

  assert(pointer == &value);
  *pointer = 29;
  assert(value == 29);
}

void test_internal_addressof_overloaded() {
  // Nonportable helper probe at the overloaded-address object type.
  overloaded_address object{31};
  overloaded_address* pointer = std::__addressof(object);

  assert(pointer != nullptr);
  assert(pointer->value == 31);
  pointer->value = 37;
  assert(object.value == 37);
}

int main() {
  test_public_addressof_int();
  test_public_addressof_overloaded();
  test_internal_addressof_int();
  test_internal_addressof_overloaded();
}
