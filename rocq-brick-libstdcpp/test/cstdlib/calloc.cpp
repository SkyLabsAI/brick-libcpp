#include <cerrno>
#include <cstdint>
#include <cstdlib>

// calloc returns zeroed bytes.
int test_calloc_zeroed() {
    unsigned char* p = static_cast<unsigned char*>(calloc(2, 2));
    if (p == nullptr)
        return -1;
    int r = p[0] + p[3];
    free(p);
    return r;
}

// SIZE_MAX * 2 overflows size_t, so calloc fails with ENOMEM.
bool test_calloc_overflow() {
    errno = 0;
    void* p = calloc(SIZE_MAX, 2);
    return p == nullptr && errno == ENOMEM;
}

// Zeroed bytes that were never read can be given back to free whole.
void test_calloc_free() {
    void* p = calloc(3, 1);
    free(p);
}
