#include <cerrno>
#include <cstdlib>
#include <new>

// Written bytes are given back to free whole.
int test_free_written() {
    unsigned char* p = static_cast<unsigned char*>(malloc(2));
    if (p == nullptr)
        return -1;
    p[0] = 7;
    p[1] = 9;
    int r = p[0] + p[1];
    free(p);
    return r;
}

// A zero-size block, NULL or not, may be passed to free.
void test_free_zero_size() {
    void* p = malloc(0);
    free(p);
}

// free(NULL) does nothing; in particular it leaves errno alone.
int test_free_null() {
    errno = EINVAL;
    free(nullptr);
    return errno;
}

// Two live blocks are freed in either order.
void test_free_two_blocks() {
    void* p = malloc(1);
    void* q = malloc(1);
    free(q);
    free(p);
}

// Deliberately mismatched pair for a proof rejection test; do not execute.
void test_new_to_free() {
    void* p = ::operator new(16, std::nothrow);
    free(p);
}
