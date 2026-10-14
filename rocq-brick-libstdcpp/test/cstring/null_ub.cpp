// Calls into <cstring> with a null pointer argument and length 0.
//
// All of these are undefined behavior in C++23: [cstring.syn] defers to the C
// library, whose pointer arguments must be valid even when the length is zero
// (C17 7.1.4p1, 7.24.1p2; WG14 N3322 lifts this only for C2y).
// - clang flags each call with -Wnonnull while cpp2v generates the AST; the
//   `runtest` rule in ../dune checks this against null_ub.warnings.expected;
// - null_ub_proof.v shows that the specs in cstring/spec.v reject each call.
#include <cstring>

static unsigned char buf[4] = {'a', 'b', 'c', 'd'};

void memchr_null() { (void)std::memchr(static_cast<void *>(nullptr), 'a', 0); }
void memchr_const_null() {
    (void)std::memchr(static_cast<const void *>(nullptr), 'a', 0);
}
int memcmp_null_lhs() { return std::memcmp(nullptr, buf, 0); }
int memcmp_null_rhs() { return std::memcmp(buf, nullptr, 0); }
void memset_null() { (void)std::memset(nullptr, 0, 0); }
void memcpy_null_dest() { (void)std::memcpy(nullptr, buf, 0); }
void memcpy_null_src() { (void)std::memcpy(buf, nullptr, 0); }
void memmove_null_dest() { (void)std::memmove(nullptr, buf, 0); }
void memmove_null_src() { (void)std::memmove(buf, nullptr, 0); }
int strncmp_null_lhs() { return std::strncmp(nullptr, "a", 0); }
int strncmp_null_rhs() { return std::strncmp("a", nullptr, 0); }
