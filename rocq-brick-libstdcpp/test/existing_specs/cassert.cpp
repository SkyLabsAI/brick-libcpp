#include <cassert>

// This coverage slice exercises active assertions only.  Defining NDEBUG would
// erase the backend edge that the Phase-B proof is intended to make
// unreachable.
#ifdef NDEBUG
#error "the cassert coverage client requires active assertions"
#endif

#if defined(__GLIBC__)
#define CASSERT_HAS_GLIBC_ASSERT_FAIL 1
#else
#define CASSERT_HAS_GLIBC_ASSERT_FAIL 0
#endif

#if defined(__APPLE__) && defined(__MACH__) && defined(__GNUC__)
#define CASSERT_HAS_DARWIN_ASSERT_RTN 1
#else
#define CASSERT_HAS_DARWIN_ASSERT_RTN 0
#endif

// Linux does not declare or export __assert_rtn.  This opt-in declaration is
// solely for syntax/AST inspection of the Darwin ABI shape; that configuration
// must never be linked or executed.
#if defined(CASSERT_AST_CHECK_ASSERT_RTN) && !CASSERT_HAS_DARWIN_ASSERT_RTN
extern "C" [[noreturn]] void __assert_rtn(
    const char* function,
    const char* file,
    int line,
    const char* expression);
#define CASSERT_CAN_FORM_ASSERT_RTN 1
#elif CASSERT_HAS_DARWIN_ASSERT_RTN
#define CASSERT_CAN_FORM_ASSERT_RTN 1
#else
#define CASSERT_CAN_FORM_ASSERT_RTN 0
#endif

#if defined(__FILE_NAME__)
#define CASSERT_DARWIN_FILE_ARGUMENT __FILE_NAME__
#else
#define CASSERT_DARWIN_FILE_ARGUMENT __FILE__
#endif

namespace cassert_client {

// The strongest portable success oracle is control flow: this function returns
// normally, so the active platform backend is not called.
void assert_true_success() {
  assert(true);
}

#if CASSERT_HAS_GLIBC_ASSERT_FAIL
// A Phase-B wrapper contract must require condition=true.  The false branch
// preserves the real glibc argument order and line type while making the
// backend's impossible precondition load-bearing in the proof.
void glibc_backend_guarded(bool condition) {
  if (!condition) {
    __assert_fail("condition",
                  __FILE__,
                  static_cast<unsigned int>(__LINE__),
                  __PRETTY_FUNCTION__);
  }
}

// This shape also lets the front end expose the installed assert macro's exact
// expression/file/line/function payload in an AST dump.
void glibc_assert_macro_guarded(bool condition) {
  assert(condition);
}

void glibc_success_composition() {
  assert_true_success();
  glibc_assert_macro_guarded(true);
  glibc_backend_guarded(true);
}
#endif

#if CASSERT_CAN_FORM_ASSERT_RTN
// Apple Libc's backend order is function, file, signed line, expression.  On a
// non-Darwin host this function exists only in the AST-check configuration
// above, which is intentionally never linked or run.
void darwin_backend_guarded(bool condition) {
  if (!condition) {
    __assert_rtn(__func__,
                 CASSERT_DARWIN_FILE_ARGUMENT,
                 static_cast<int>(__LINE__),
                 "condition");
  }
}

void darwin_success_composition() {
  assert_true_success();
  darwin_backend_guarded(true);
}
#endif

}  // namespace cassert_client

#if defined(CASSERT_NATIVE_HARNESS)
int main() {
  cassert_client::assert_true_success();
#if CASSERT_HAS_GLIBC_ASSERT_FAIL
  cassert_client::glibc_success_composition();
#elif CASSERT_HAS_DARWIN_ASSERT_RTN
  cassert_client::darwin_success_composition();
#endif
  return 0;
}
#endif
