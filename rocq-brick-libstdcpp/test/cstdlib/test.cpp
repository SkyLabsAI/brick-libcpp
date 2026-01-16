#include <cstdlib>
#include <cassert>
#include <climits>

void test_atoi() {
    // Basic functionality
    assert(0 == atoi("0"));
    assert(1 == atoi("1"));
    assert(42 == atoi("42"));
    assert(-42 == atoi("-42"));

    // Leading whitespace
    assert(123 == atoi("  123"));
    assert(123 == atoi("\t123"));
    assert(123 == atoi("\n123"));
    assert(123 == atoi("\r123"));
    assert(123 == atoi("\f123"));
    assert(123 == atoi("\v123"));

    // Plus sign
    assert(456 == atoi("+456"));

    // Non-digit characters after number
    assert(789 == atoi("789abc"));

    // Non-digit characters before number
    assert(0 == atoi("abc123"));

    // Empty string
    assert(0 == atoi(""));

    // Just whitespace
    assert(0 == atoi("   "));

    // Just sign
    assert(0 == atoi("+"));
    assert(0 == atoi("-"));

    // Hexadecimal notation (should not be recognized by atoi)
    assert(0 == atoi("0x123"));

    // Octal notation (should not be recognized by atoi)
    assert(123 == atoi("0123")); // Parsed as decimal 123

    // Very large numbers
    assert(INT_MAX == atoi("2147483647")); // INT_MAX
    assert(INT_MIN == atoi("-2147483648")); // INT_MIN

    // Numbers beyond range (implementation-defined behavior, but common behavior is saturation)
    // Note: These tests might not behave consistently across all implementations
    // so they're commented out for portability.
    // assert(INT_MAX == atoi("2147483648")); // INT_MAX + 1, often saturates to INT_MAX
    // assert(INT_MIN == atoi("-2147483649")); // INT_MIN - 1, often saturates to INT_MIN
}

void test_atol() {
    // Basic functionality
    assert(0L == atol("0"));
    assert(1L == atol("1"));
    assert(42L == atol("42"));
    assert(-42L == atol("-42"));

    // Leading whitespace
    assert(123L == atol("  123"));
    assert(123L == atol("\n\t\r  123"));

    // Plus sign
    assert(456L == atol("+456"));

    // Non-digit characters after number
    assert(789L == atol("789abc"));

    // Non-digit characters before number
    assert(0L == atol("abc123"));

    // Empty string
    assert(0L == atol(""));

    // Just whitespace
    assert(0L == atol("   "));

    // Just sign
    assert(0L == atol("+"));
    assert(0L == atol("-"));

    // Hexadecimal notation (should not be recognized by atol)
    assert(0L == atol("0x123"));

    // Octal notation (should not be recognized by atol)
    assert(123L == atol("0123")); // Parsed as decimal 123

    // Large numbers
    assert(LONG_MAX == atol("9223372036854775807")); // LONG_MAX on 64-bit systems
    assert(LONG_MIN == atol("-9223372036854775808")); // LONG_MIN on 64-bit systems
}

void test_atoll() {
    // Basic functionality
    assert(0LL == atoll("0"));
    assert(1LL == atoll("1"));
    assert(42LL == atoll("42"));
    assert(-42LL == atoll("-42"));

    // Leading whitespace
    assert(123LL == atoll("  123"));
    assert(123LL == atoll("\r\t  123"));
    assert(123LL == atoll("\n  123"));

    // Plus sign
    assert(456LL == atoll("+456"));

    // Non-digit characters after number
    assert(789LL == atoll("789abc"));

    // Non-digit characters before number
    assert(0LL == atoll("abc123"));

    // Empty string
    assert(0LL == atoll(""));

    // Just whitespace
    assert(0LL == atoll("   "));

    // Just sign
    assert(0LL == atoll("+"));
    assert(0LL == atoll("-"));

    // Hexadecimal notation (should not be recognized by atoll)
    assert(0LL == atoll("0x123"));

    // Octal notation (should not be recognized by atoll)
    assert(123LL == atoll("0123")); // Parsed as decimal 123

    // Very large numbers
    assert(LLONG_MAX == atoll("9223372036854775807")); // LLONG_MAX
    assert(LLONG_MIN == atoll("-9223372036854775808")); // LLONG_MIN
}

int main() {
    test_atoi();
    test_atol();
    test_atoll();
    return 0;
}
