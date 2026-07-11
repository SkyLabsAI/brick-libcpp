#include <cassert>
#include <cstddef>
#include <cstring>

void check_length_and_comparisons() {
  assert(std::strlen("") == 0U);
  assert(std::strlen("brick") == 5U);

  assert(std::strcmp("abc", "abc") == 0);
  assert(std::strcmp("abc", "abd") < 0);
  assert(std::strcmp("abd", "abc") > 0);

  assert(std::strncmp("abc", "abd", 2U) == 0);
  assert(std::strncmp("abc", "abd", 3U) < 0);
  assert(std::strncmp("abd", "abc", 3U) > 0);
}

void check_strchr_overloads() {
  char mutable_text[] = "banana";
  char *mutable_first = std::strchr(mutable_text, 'a');
  assert(mutable_first == mutable_text + 1);
  assert(std::strchr(mutable_text, 'x') == nullptr);
  assert(std::strchr(mutable_text, '\0') == mutable_text + 6);
  assert(mutable_text[0] == 'b');
  assert(mutable_text[6] == '\0');

  const char const_text[] = "banana";
  const char *const_first = std::strchr(const_text, 'a');
  assert(const_first == const_text + 1);
  assert(std::strchr(const_text, 'x') == nullptr);
  assert(std::strchr(const_text, '\0') == const_text + 6);
}

void check_strrchr_overloads() {
  char mutable_text[] = "banana";
  char *mutable_last = std::strrchr(mutable_text, 'a');
  assert(mutable_last == mutable_text + 5);
  assert(std::strrchr(mutable_text, 'x') == nullptr);
  assert(std::strrchr(mutable_text, '\0') == mutable_text + 6);

  const char const_text[] = "banana";
  const char *const_last = std::strrchr(const_text, 'a');
  assert(const_last == const_text + 5);
  assert(std::strrchr(const_text, 'x') == nullptr);
  assert(std::strrchr(const_text, '\0') == const_text + 6);
}

void check_spans() {
  assert(std::strspn("abcde", "abc") == 3U);
  assert(std::strcspn("abcde", "dx") == 3U);
}

void check_strpbrk_overloads() {
  char mutable_text[] = "abcdef";
  char *mutable_match = std::strpbrk(mutable_text, "xyc");
  assert(mutable_match == mutable_text + 2);
  assert(std::strpbrk(mutable_text, "xyz") == nullptr);

  const char const_text[] = "abcdef";
  const char *const_match = std::strpbrk(const_text, "xyc");
  assert(const_match == const_text + 2);
  assert(std::strpbrk(const_text, "xyz") == nullptr);
}

void check_strstr_overloads() {
  char mutable_text[] = "abracadabra";
  char *mutable_match = std::strstr(mutable_text, "cad");
  assert(mutable_match == mutable_text + 4);
  assert(std::strstr(mutable_text, "xyz") == nullptr);
  assert(std::strstr(mutable_text, "") == mutable_text);

  const char const_text[] = "abracadabra";
  const char *const_match = std::strstr(const_text, "cad");
  assert(const_match == const_text + 4);
  assert(std::strstr(const_text, "xyz") == nullptr);
  assert(std::strstr(const_text, "") == const_text);
}

void check_memchr_overloads() {
  unsigned char mutable_bytes[] = {0x10U, 0x22U, 0x33U, 0x22U};
  void *mutable_match =
      std::memchr(mutable_bytes, 0x22, sizeof(mutable_bytes));
  assert(mutable_match == mutable_bytes + 1);
  assert(std::memchr(mutable_bytes, 0x44, sizeof(mutable_bytes)) == nullptr);

  const unsigned char const_bytes[] = {0x10U, 0x22U, 0x33U, 0x22U};
  const void *const_match =
      std::memchr(const_bytes, 0x22, sizeof(const_bytes));
  assert(const_match == const_bytes + 1);
  assert(std::memchr(const_bytes, 0x44, sizeof(const_bytes)) == nullptr);
}

void check_memcmp() {
  const unsigned char lower[] = {0x10U, 0x20U, 0x30U};
  const unsigned char higher[] = {0x10U, 0x21U, 0x30U};

  assert(std::memcmp(lower, higher, sizeof(lower)) < 0);
  assert(std::memcmp(lower, higher, 1U) == 0);
  assert(std::memcmp(higher, lower, sizeof(lower)) > 0);
}

void check_memset() {
  unsigned char bytes[] = {0U, 1U, 2U, 3U};
  void *returned = std::memset(bytes, 0x123, 3U);

  assert(returned == bytes);
  assert(bytes[0] == 0x23U);
  assert(bytes[1] == 0x23U);
  assert(bytes[2] == 0x23U);
  assert(bytes[3] == 3U);
}

void check_memcpy() {
  const unsigned char source[] = {1U, 2U, 3U, 4U};
  unsigned char destination[] = {0U, 0U, 0U, 0U};
  void *returned = std::memcpy(destination, source, sizeof(source));

  assert(returned == destination);
  assert(destination[0] == 1U);
  assert(destination[1] == 2U);
  assert(destination[2] == 3U);
  assert(destination[3] == 4U);
  assert(source[0] == 1U);
  assert(source[3] == 4U);
}

void check_memmove_nonoverlap() {
  const unsigned char source[] = {5U, 6U, 7U, 8U};
  unsigned char destination[] = {0U, 0U, 0U, 0U};
  void *returned = std::memmove(destination, source, sizeof(source));

  assert(returned == destination);
  assert(destination[0] == 5U);
  assert(destination[1] == 6U);
  assert(destination[2] == 7U);
  assert(destination[3] == 8U);
  assert(source[0] == 5U);
  assert(source[3] == 8U);
}

int main() {
  check_length_and_comparisons();
  check_strchr_overloads();
  check_strrchr_overloads();
  check_spans();
  check_strpbrk_overloads();
  check_strstr_overloads();
  check_memchr_overloads();
  check_memcmp();
  check_memset();
  check_memcpy();
  check_memmove_nonoverlap();
}
