#include <cstdio>

// Writes the string, without its terminator.
void test_fputs_hello(FILE* f) {
    fputs("Hello", f);
}

// Consecutive calls write in order.
void test_fputs_twice(FILE* f) {
    fputs("ab", f);
    fputs("cd", f);
}

// The standard streams are ordinary FILE pointers; success is nonnegative.
bool test_fputs_stderr() {
    return fputs("error\n", stderr) >= 0;
}
