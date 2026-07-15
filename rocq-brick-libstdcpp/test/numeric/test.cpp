#include <cassert>
#include <numeric>

void test_gcd_int() {
  assert(std::gcd(0, -27) == 27);
  assert(std::gcd(-48, 18) == 6);
  assert(std::gcd(35, 64) == 1);
  assert(std::gcd(42, 42) == 42);
}

void test_lcm_int() {
  assert(std::lcm(-27, 0) == 0);
  assert(std::lcm(-21, 6) == 42);
  assert(std::lcm(12, 18) == 36);
  assert(std::lcm(181, 180) == 32580);
}

void test_mixed_width() {
  assert(std::gcd(-48, 18LL) == 6);
}
