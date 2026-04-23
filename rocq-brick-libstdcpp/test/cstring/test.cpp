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

void test_memchr() {
    unsigned char s[] = {'a', 'b', 'c', 'a'};
    assert(std::memchr(s, 'a', 4) == s);
    assert(std::memchr(s, 'c', 4) == s + 2);
    assert(std::memchr(s, 'z', 4) == nullptr);
    assert(std::memchr(s, 'a', 0) == nullptr);
    assert(std::memchr(s + 1, 'a', 3) == s + 3);
}

void test_memchr_embedded_null() {
    unsigned char s[] = {'a', '\0', 'b', '\0'};
    assert(std::memchr(s, '\0', 4) == s + 1);
    assert(std::memchr(s + 2, '\0', 2) == s + 3);
    assert(std::memchr(s, 'b', 4) == s + 2);
}

void test_memcmp() {
    unsigned char abc[] = {'a', 'b', 'c'};
    unsigned char abd[] = {'a', 'b', 'd'};
    unsigned char ab[] = {'a', 'b'};

    assert(std::memcmp(abc, abc, 3) == 0);
    assert(std::memcmp(abc, abd, 3) < 0);
    assert(std::memcmp(abd, abc, 3) > 0);
    assert(std::memcmp(abc, abd, 2) == 0);
    assert(std::memcmp(abc, ab, 0) == 0);
}

void test_memcmp_embedded_null() {
    unsigned char x[] = {'a', '\0', 'x'};
    unsigned char y[] = {'a', '\0', 'y'};

    assert(std::memcmp(x, y, 2) == 0);
    assert(std::memcmp(x, y, 3) < 0);
    assert(std::memcmp(y, x, 3) > 0);
}

void test_memset() {
    unsigned char s[] = {'a', 'b', 'c', 'd'};

    assert(std::memset(s, 'x', 2) == s);
    assert(s[0] == 'x');
    assert(s[1] == 'x');
    assert(s[2] == 'c');
    assert(s[3] == 'd');

    assert(std::memset(s + 2, 0x123, 1) == s + 2);
    assert(s[2] == static_cast<unsigned char>(0x123));
    assert(s[3] == 'd');
}

void test_memset_embedded_null() {
    unsigned char s[] = {'a', 'b', 'c', 'd'};

    assert(std::memset(s + 1, '\0', 2) == s + 1);
    assert(s[0] == 'a');
    assert(s[1] == '\0');
    assert(s[2] == '\0');
    assert(s[3] == 'd');
}

void test_memcpy() {
    unsigned char src[] = {'a', 'b', 'c', 'd'};
    unsigned char dst[] = {'w', 'x', 'y', 'z'};

    assert(std::memcpy(dst, src, 3) == dst);
    assert(dst[0] == 'a');
    assert(dst[1] == 'b');
    assert(dst[2] == 'c');
    assert(dst[3] == 'z');
    assert(src[0] == 'a');
    assert(src[3] == 'd');

    assert(std::memcpy(dst + 1, src + 2, 0) == dst + 1);
    assert(dst[0] == 'a');
    assert(dst[1] == 'b');
}

void test_memcpy_embedded_null() {
    unsigned char src[] = {'a', '\0', 'b', '\0'};
    unsigned char dst[] = {'w', 'x', 'y', 'z'};

    assert(std::memcpy(dst, src, 4) == dst);
    assert(dst[0] == 'a');
    assert(dst[1] == '\0');
    assert(dst[2] == 'b');
    assert(dst[3] == '\0');
}

void test_memmove() {
    unsigned char src[] = {'a', 'b', 'c', 'd'};
    unsigned char dst[] = {'w', 'x', 'y', 'z'};

    assert(std::memmove(dst, src, 4) == dst);
    assert(dst[0] == 'a');
    assert(dst[1] == 'b');
    assert(dst[2] == 'c');
    assert(dst[3] == 'd');

    assert(std::memmove(dst + 1, src + 1, 0) == dst + 1);
    assert(dst[1] == 'b');
}

void test_memmove_overlap() {
    char forward[] = {'a', 'b', 'c', 'd', 'e', 'f', '\0'};
    char backward[] = {'a', 'b', 'c', 'd', 'e', 'f', '\0'};

    assert(std::memmove(forward + 2, forward, 4) == forward + 2);
    assert(forward[0] == 'a');
    assert(forward[1] == 'b');
    assert(forward[2] == 'a');
    assert(forward[3] == 'b');
    assert(forward[4] == 'c');
    assert(forward[5] == 'd');
    assert(forward[6] == '\0');

    assert(std::memmove(backward, backward + 2, 4) == backward);
    assert(backward[0] == 'c');
    assert(backward[1] == 'd');
    assert(backward[2] == 'e');
    assert(backward[3] == 'f');
    assert(backward[4] == 'e');
    assert(backward[5] == 'f');
    assert(backward[6] == '\0');
}

void test_memmove_embedded_null() {
    char s[] = {'a', '\0', 'b', 'c', '\0'};

    assert(std::memmove(s + 1, s, 4) == s + 1);
    assert(s[0] == 'a');
    assert(s[1] == 'a');
    assert(s[2] == '\0');
    assert(s[3] == 'b');
    assert(s[4] == 'c');
}

void test_cstring_slice1() {
    test_strlen();
    test_strcmp();
    test_strncmp();
}

void test_cstring_slice4() {
    test_memchr();
    test_memcmp();
    test_memset();
    test_memcpy();
    test_memmove();
}
