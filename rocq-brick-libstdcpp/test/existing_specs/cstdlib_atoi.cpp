#include <cassert>
#include <cstdlib>

int atoi_zero_and_no_conversion() {
  const int parsed_zero = std::atoi("0");
  const int no_conversion = std::atoi("words");

  assert(parsed_zero == 0);
  assert(no_conversion == 0);
  return parsed_zero + no_conversion;
}

int atoi_signed_values() {
  const int positive = std::atoi("42");
  const int negative = std::atoi("-17");
  const int explicitly_positive = std::atoi("+23");

  assert(positive == 42);
  assert(negative == -17);
  assert(explicitly_positive == 23);
  return positive + negative + explicitly_positive;
}

int atoi_whitespace_and_prefix() {
  const int whitespace_prefixed = std::atoi(" \t\n42");
  const int numeric_prefix = std::atoi("123xyz");

  assert(whitespace_prefixed == 42);
  assert(numeric_prefix == 123);
  return whitespace_prefixed + numeric_prefix;
}

long atol_decimal_value() {
  const long value = std::atol("1234567890");

  assert(value == 1234567890L);
  return value;
}

long long atoll_wide_value() {
  const long long value = std::atoll("5000000000");

  assert(value == 5000000000LL);
  return value;
}

int atoi_preserves_buffer_and_composes() {
  char input[] = {'2', '1', '\0'};
  const int value = std::atoi(input);

  assert(value == 21);
  assert(input[0] == '2');
  assert(input[1] == '1');
  assert(input[2] == '\0');

  const int doubled = value * 2;
  assert(doubled == 42);
  return doubled;
}

int main() {
  assert(atoi_zero_and_no_conversion() == 0);
  assert(atoi_signed_values() == 48);
  assert(atoi_whitespace_and_prefix() == 165);
  assert(atol_decimal_value() == 1234567890L);
  assert(atoll_wide_value() == 5000000000LL);
  assert(atoi_preserves_buffer_and_composes() == 42);
  return 0;
}
