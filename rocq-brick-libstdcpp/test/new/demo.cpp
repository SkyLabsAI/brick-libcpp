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

void test_raw_scalar_aligned(std::align_val_t al) {
  auto p = ::operator new(16, al);
  ::operator delete(p, al);
}

void test_raw_scalar_aligned_sized(std::align_val_t al) {
  auto p = ::operator new(16, al);
  ::operator delete(p, 16, al);
}

void test_raw_scalar_aligned_nothrow(std::align_val_t al) {
  auto p = ::operator new(16, al, std::nothrow);
  ::operator delete(p, al);
}

// Invalid even when the requested delete alignment equals the default.
void test_scalar_to_aligned_delete() {
  auto p = ::operator new(16);
  ::operator delete(p, std::align_val_t{__STDCPP_DEFAULT_NEW_ALIGNMENT__});
}

void test_aligned_scalar_to_unaligned_delete(std::align_val_t al) {
  auto p = ::operator new(16, al);
  ::operator delete(p);
}

// Invalid even when the requested delete alignment equals the default.
void test_scalar_to_aligned_delete_sized() {
  auto p = ::operator new(16);
  ::operator delete(p, 16, std::align_val_t{__STDCPP_DEFAULT_NEW_ALIGNMENT__});
}

void test_aligned_scalar_to_unaligned_delete_sized(std::align_val_t al) {
  auto p = ::operator new(16, al);
  ::operator delete(p, 16);
}

void test_scalar_wrong_alignment(void* p, std::align_val_t al) {
  ::operator delete(p, al);
}

void test_scalar_wrong_alignment_sized(void* p, std::align_val_t al) {
  ::operator delete(p, 16, al);
}

void test_raw_array_aligned(std::align_val_t al) {
  auto p = ::operator new[](16, al);
  ::operator delete[](p, al);
}

void test_raw_array_aligned_sized(std::align_val_t al) {
  auto p = ::operator new[](16, al);
  ::operator delete[](p, 16, al);
}

void test_raw_array_aligned_nothrow(std::align_val_t al) {
  auto p = ::operator new[](16, al, std::nothrow);
  ::operator delete[](p, al);
}

// Invalid even when the requested delete alignment equals the default.
void test_array_to_aligned_delete() {
  auto p = ::operator new[](16);
  ::operator delete[](p, std::align_val_t{__STDCPP_DEFAULT_NEW_ALIGNMENT__});
}

void test_aligned_array_to_unaligned_delete(std::align_val_t al) {
  auto p = ::operator new[](16, al);
  ::operator delete[](p);
}

// Invalid even when the requested delete alignment equals the default.
void test_array_to_aligned_delete_sized() {
  auto p = ::operator new[](16);
  ::operator delete[](p, 16, std::align_val_t{__STDCPP_DEFAULT_NEW_ALIGNMENT__});
}

void test_aligned_array_to_unaligned_delete_sized(std::align_val_t al) {
  auto p = ::operator new[](16, al);
  ::operator delete[](p, 16);
}

void test_array_wrong_alignment(void* p, std::align_val_t al) {
  ::operator delete[](p, al);
}

void test_array_wrong_alignment_sized(void* p, std::align_val_t al) {
  ::operator delete[](p, 16, al);
}

void test_raw_aligned_delete_null(std::align_val_t al) {
  ::operator delete(nullptr, al);
  ::operator delete(nullptr, 16, al);
  ::operator delete[](nullptr, al);
  ::operator delete[](nullptr, 16, al);
}

struct alignas(64) AlignedValue {
  int value;
  ~AlignedValue() {}
};

void test_new_delete_aligned() {
  auto p = new AlignedValue{0};
  delete p;
}

struct alignas(64) AlignedPod {
  int value;
};

// The token alone (no ambient alignment fact) must suffice to delete.
void test_delete_aligned(AlignedValue* p) {
  delete p;
}

// Null deletes that select the aligned global operators.
void test_delete_null_aligned() {
  AlignedValue* p = nullptr;
  delete p;
  AlignedValue* q = nullptr;
  delete[] q;
  AlignedPod* r = nullptr;
  delete[] r;
}

void test_raw_scalar_zero() {
  auto p = ::operator new(0);
  ::operator delete(p, std::size_t{0});
}

void test_raw_array_zero() {
  auto p = ::operator new[](0);
  ::operator delete[](p, std::size_t{0});
}

void test_raw_scalar_aligned_zero(std::align_val_t al) {
  auto p = ::operator new(0, al);
  ::operator delete(p, std::size_t{0}, al);
}

void test_raw_array_aligned_zero(std::align_val_t al) {
  auto p = ::operator new[](0, al);
  ::operator delete[](p, std::size_t{0}, al);
}

// The allocation receipt still matters when the memory block is empty.
void test_scalar_zero_to_aligned_delete() {
  auto p = ::operator new(0);
  ::operator delete(p, std::size_t{0}, std::align_val_t{__STDCPP_DEFAULT_NEW_ALIGNMENT__});
}

void test_array_zero_to_aligned_delete() {
  auto p = ::operator new[](0);
  ::operator delete[](p, std::size_t{0}, std::align_val_t{__STDCPP_DEFAULT_NEW_ALIGNMENT__});
}

void test_raw_scalar_partial_receipt(void* p, std::align_val_t al) {
  ::operator delete(p, 16, al);
}

void test_raw_array_partial_receipt(void* p, std::align_val_t al) {
  ::operator delete[](p, 16, al);
}

// Implementation support need not have a matching type declaration here.
void test_raw_additional_alignment() {
  auto p = ::operator new(16, std::align_val_t{4096});
  ::operator delete(p, 16, std::align_val_t{4096});
}

// End-to-end matrix: each new/delete form, composed with the library specs.
void test_new_nothrow_delete() {
  auto p = new (std::nothrow) int;
  delete p;
}

void test_new_nothrow_aligned_delete() {
  auto p = new (std::nothrow) AlignedValue{0};
  delete p;
}

void test_delete_null() {
  int* p = nullptr;
  delete p;
  int* q = nullptr;
  delete[] q;
}

// The default allocation token for an over-aligned type records the
// alignment argument passed by the global aligned operator new.
AlignedValue* test_new_aligned_token() {
  return new AlignedValue{0};
}

struct WithDtor {
  ~WithDtor() {}
};

void test_new_delete_array_dtor() {
  auto p = new WithDtor[2];
  delete[] p;
}

void test_new_delete_aligned_array() {
  auto p = new AlignedPod[2];
  delete[] p;
}

struct alignas(64) AlignedDtor {
  ~AlignedDtor() {}
};

void test_new_delete_aligned_array_dtor() {
  auto p = new AlignedDtor[2];
  delete[] p;
}
