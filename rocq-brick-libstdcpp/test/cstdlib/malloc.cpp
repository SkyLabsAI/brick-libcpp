#include <cerrno>
#include <cstdlib>
#include <new>

// Write two bytes into a fresh block and read them back.
int test_malloc_write_read() {
    unsigned char* p = static_cast<unsigned char*>(malloc(2));
    if (p == nullptr)
        return -1;
    p[0] = 7;
    p[1] = 9;
    return p[0] + p[1];
}

// A failed malloc sets errno to ENOMEM.
bool test_malloc_errno() {
    errno = 0;
    void* p = malloc(16);
    if (p == nullptr)
        return errno == ENOMEM;
    return true;
}

// Writes to one live block do not change another.
int test_malloc_two_blocks() {
    unsigned char* p = static_cast<unsigned char*>(malloc(1));
    unsigned char* q = static_cast<unsigned char*>(malloc(1));
    if (p == nullptr || q == nullptr)
        return -1;
    p[0] = 1;
    q[0] = 2;
    return p[0] + q[0];
}

// Deliberately mismatched pair for a proof rejection test; do not execute.
void test_malloc_to_delete() {
    void* p = malloc(16);
    ::operator delete(p);
}
