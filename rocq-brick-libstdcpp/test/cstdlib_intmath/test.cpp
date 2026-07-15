#include <cassert>
#include <climits>
#include <cstdlib>

void test_abs_int() {
    assert(std::abs(0) == 0);
    assert(std::abs(42) == 42);
    assert(std::abs(-42) == 42);
    assert(std::abs(-32767) == 32767);
}

void test_abs_long() {
    assert(std::abs(0L) == 0L);
    assert(std::abs(-73L) == 73L);
    assert(std::labs(-73L) == 73L);
    assert(std::abs(-2147483647L) == std::labs(-2147483647L));
}

void test_abs_long_long() {
    assert(std::abs(0LL) == 0LL);
    assert(std::abs(-73LL) == 73LL);
    assert(std::llabs(-73LL) == 73LL);
    assert(std::abs(-9223372036854775807LL) ==
           std::llabs(-9223372036854775807LL));
}

void test_div_int() {
    std::div_t pp = std::div(369, 10);
    assert(pp.quot == 36);
    assert(pp.rem == 9);

    std::div_t pn = std::div(369, -10);
    assert(pn.quot == -36);
    assert(pn.rem == 9);

    std::div_t np = std::div(-369, 10);
    assert(np.quot == -36);
    assert(np.rem == -9);

    std::div_t nn = std::div(-369, -10);
    assert(nn.quot == 36);
    assert(nn.rem == -9);
}

void test_div_long() {
    std::ldiv_t via_overload = std::div(-369L, 10L);
    std::ldiv_t via_named = std::ldiv(-369L, 10L);
    assert(via_overload.quot == -36L);
    assert(via_overload.rem == -9L);
    assert(via_overload.quot == via_named.quot);
    assert(via_overload.rem == via_named.rem);
}

void test_div_long_long() {
    std::lldiv_t via_overload = std::div(369LL, -10LL);
    std::lldiv_t via_named = std::lldiv(369LL, -10LL);
    assert(via_overload.quot == -36LL);
    assert(via_overload.rem == 9LL);
    assert(via_overload.quot == via_named.quot);
    assert(via_overload.rem == via_named.rem);
}

void test_intmath_composition() {
    std::div_t qr = std::div(-369, 10);
    assert(qr.quot * 10 + qr.rem == -369);
    assert(std::abs(qr.rem) == 9);
}

// These functions are translated as boundary witnesses but intentionally have
// no successful verify lemma: each call is outside the standard-defined domain.
int bad_abs_int_min() {
    return std::abs(INT_MIN);
}

std::div_t bad_div_zero() {
    return std::div(7, 0);
}

std::div_t bad_div_overflow() {
    return std::div(INT_MIN, -1);
}
