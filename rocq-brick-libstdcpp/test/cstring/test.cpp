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

void test_strchr() {
    const char *s = "banana";
    const char *empty = "";
    assert(std::strchr(s, 'b') == s);
    assert(std::strchr(s, 'n') == s + 2);
    assert(std::strchr(s, 'z') == nullptr);
    assert(std::strchr(s, '\0') == s + 6);
    assert(std::strchr(empty, 'a') == nullptr);
    assert(std::strchr(empty, '\0') == empty);
}

void test_strrchr() {
    const char *s = "banana";
    const char *empty = "";
    assert(std::strrchr(s, 'a') == s + 5);
    assert(std::strrchr(s, 'b') == s);
    assert(std::strrchr(s, 'z') == nullptr);
    assert(std::strrchr(s, '\0') == s + 6);
    assert(std::strrchr(empty, 'a') == nullptr);
    assert(std::strrchr(empty, '\0') == empty);
}

void test_strspn() {
    assert(std::strspn("abcde", "abc") == 3);
    assert(std::strspn("abcde", "ba") == 2);
    assert(std::strspn("abc", "") == 0);
    assert(std::strspn("", "abc") == 0);
    assert(std::strspn("aaaa", "a") == 4);
    assert(std::strspn("abc", "xyz") == 0);
}

void test_strcspn() {
    assert(std::strcspn("abcde", "dx") == 3);
    assert(std::strcspn("abcde", "a") == 0);
    assert(std::strcspn("abc", "") == 3);
    assert(std::strcspn("", "abc") == 0);
    assert(std::strcspn("abc", "xyz") == 3);
}

void test_strpbrk() {
    const char *s = "abcdef";
    assert(std::strpbrk(s, "xyc") == s + 2);
    assert(std::strpbrk(s, "fa") == s);
    assert(std::strpbrk(s, "xyz") == nullptr);
    assert(std::strpbrk(s, "") == nullptr);
    assert(std::strpbrk("", "abc") == nullptr);
}

void test_strstr() {
    const char *s = "abracadabra";
    const char *empty = "";
    assert(std::strstr(s, "abra") == s);
    assert(std::strstr(s, "cad") == s + 4);
    assert(std::strstr(s, "dab") == s + 6);
    assert(std::strstr(s, "xyz") == nullptr);
    assert(std::strstr(s, "") == s);
    assert(std::strstr(empty, "") == empty);
    assert(std::strstr(empty, "a") == nullptr);
}

void test_search_embedded_null_array_buffer() {
    char s[] = {'a', 'b', '\0', 'b', 'c', '\0'};
    assert(std::strchr(s, 'b') == s + 1);
    assert(std::strchr(s, 'c') == nullptr);
    assert(std::strchr(s, '\0') == s + 2);
    assert(std::strrchr(s, 'b') == s + 1);
    assert(std::strrchr(s, '\0') == s + 2);
    assert(std::strspn(s, "abc") == 2);
    assert(std::strcspn(s, "c") == 2);
    assert(std::strpbrk(s, "c") == nullptr);
    assert(std::strpbrk(s, "b") == s + 1);
    assert(std::strstr(s, "bc") == nullptr);
    assert(std::strstr(s, "b") == s + 1);
    assert(std::strstr(s, "") == s);
}

void test_cstring_slice1() {
    test_strlen();
    test_strcmp();
    test_strncmp();
}
