#include <cstdlib>

// Code after abort is unreachable, so the caller learns x >= 0.
int test_abort_guard(int x) {
    if (x < 0)
        abort();
    return x;
}

// abort never returns.
int test_abort_noreturn() {
    abort();
    return 1;
}
