#include <cassert>
#include <cerrno>

// glibc: errno expands to (*__errno_location ()).
void test_errno_roundtrip() {
    errno = 0;
    assert(errno == 0);
    errno = ERANGE;
    assert(errno == ERANGE);
}

// Two uses of errno in one thread name the same object.
void test_errno_same_object() { assert(&errno == &errno); }
