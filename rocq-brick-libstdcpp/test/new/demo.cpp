#include <new>

int* test_new() {
  return new int{0};
}

void test_delete(int* p) {
  delete p;
}

void test_new_delete() {
  auto p = new int;
  delete p;
}

int* test_new_array() {
  auto p = new int[2];
  p[0] = 1;
  p[1] = 2;
  return p;
}

void test_delete_array(int* p) {
  delete[] p;
}

void test_new_delete_array() {
  auto p = new int[2];
  delete[] p;
}

// Direct calls exercise the library contracts independently of new-expressions.
void test_raw_scalar() {
  auto p = ::operator new(16);
  ::operator delete(p);
}

void test_raw_scalar_sized() {
  auto p = ::operator new(16);
  ::operator delete(p, 16);
}

void test_raw_array() {
  auto p = ::operator new[](16);
  ::operator delete[](p);
}

void test_raw_array_sized() {
  auto p = ::operator new[](16);
  ::operator delete[](p, 16);
}

void test_raw_scalar_nothrow() {
  auto p = ::operator new(16, std::nothrow);
  ::operator delete(p);
}

void test_raw_array_nothrow() {
  auto p = ::operator new[](16, std::nothrow);
  ::operator delete[](p);
}

void test_raw_delete_null() {
  ::operator delete(nullptr);
  ::operator delete(nullptr, 16);
  ::operator delete[](nullptr);
  ::operator delete[](nullptr, 16);
}

// Deliberately invalid pairs for proof rejection tests; do not execute these.
void test_scalar_to_array_delete() {
  auto p = ::operator new(16);
  ::operator delete[](p);
}

void test_scalar_to_array_delete_sized() {
  auto p = ::operator new(16);
  ::operator delete[](p, 16);
}

void test_array_to_scalar_delete() {
  auto p = ::operator new[](16);
  ::operator delete(p);
}

void test_array_to_scalar_delete_sized() {
  auto p = ::operator new[](16);
  ::operator delete(p, 16);
}
