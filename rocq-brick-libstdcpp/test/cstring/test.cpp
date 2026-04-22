#include <cstring>
#include <cassert>

void test_strlen() {
    assert(std::strlen("") == 0);
    assert(std::strlen("a") == 1);
    assert(std::strlen("abc") == 3);
}

void test_strlen_embedded_null() {
    assert(std::strlen("ab\0cd") == 2);
}

void test_strcmp() {
    assert(std::strcmp("", "") == 0);
    assert(std::strcmp("abc", "abc") == 0);
    assert(std::strcmp("abc", "abd") < 0);
    assert(std::strcmp("abd", "abc") > 0);
    assert(std::strcmp("ab", "abc") < 0);
    assert(std::strcmp("abc", "ab") > 0);
}

void test_strcmp_embedded_null() {
    assert(std::strcmp("ab\0x", "ab\0y") == 0);
}

void test_strncmp() {
    assert(std::strncmp("abc", "abd", 0) == 0);
    assert(std::strncmp("abc", "abd", 2) == 0);
    assert(std::strncmp("abc", "abd", 3) < 0);
    assert(std::strncmp("abd", "abc", 3) > 0);
    assert(std::strncmp("ab", "abc", 2) == 0);
    assert(std::strncmp("ab", "abc", 3) < 0);
}

void test_strncmp_embedded_null() {
    assert(std::strncmp("ab\0x", "ab\0y", 4) == 0);
}

void test_strlen_array_buffer() {
    char s[] = {'a', 'b', '\0', 'c', 'd', '\0'};
    assert(std::strlen(s) == 2);
}

void test_strcmp_array_buffer() {
    char x[] = {'a', 'b', '\0', 'x', '\0'};
    char y[] = {'a', 'b', '\0', 'y', '\0'};
    assert(std::strcmp(x, y) == 0);
}

void test_strncmp_array_buffer() {
    char x[] = {'a', 'b', '\0', 'x', '\0'};
    char y[] = {'a', 'b', '\0', 'y', '\0'};
    assert(std::strncmp(x, y, 4) == 0);
}

void test_cstring_slice1() {
    test_strlen();
    test_strcmp();
    test_strncmp();
}
