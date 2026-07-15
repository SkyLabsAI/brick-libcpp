#include <bit>
#include <cassert>
#include <cstdint>

using U32 = std::uint32_t;

int use_popcount(U32 x) { return std::popcount(x); }
int use_countl_zero(U32 x) { return std::countl_zero(x); }
int use_countr_zero(U32 x) { return std::countr_zero(x); }
int use_countl_one(U32 x) { return std::countl_one(x); }
int use_countr_one(U32 x) { return std::countr_one(x); }
U32 use_bit_width(U32 x) { return std::bit_width(x); }
U32 use_bit_ceil(U32 x) { return std::bit_ceil(x); }
U32 use_bit_floor(U32 x) { return std::bit_floor(x); }
bool use_has_single_bit(U32 x) { return std::has_single_bit(x); }
U32 use_rotl(U32 x, int s) { return std::rotl(x, s); }
U32 use_rotr(U32 x, int s) { return std::rotr(x, s); }

void test_bit_count_oracles() {
  assert(std::popcount(U32{0}) == 0);
  assert(std::popcount(U32{0xAAAAAAAA}) == 16);
  assert(std::popcount(U32{0xFFFFFFFF}) == 32);
  assert(std::countl_zero(U32{0}) == 32);
  assert(std::countr_zero(U32{0}) == 32);
  assert(std::countl_one(U32{0xFFFFFFFF}) == 32);
  assert(std::countr_one(U32{0xFFFFFFFF}) == 32);
}

void test_bit_power_oracles() {
  assert(!std::has_single_bit(U32{0}));
  assert(std::has_single_bit(U32{1}));
  assert(std::has_single_bit(U32{0x80000000}));
  assert(!std::has_single_bit(U32{3}));
  assert(std::bit_width(U32{0}) == 0);
  assert(std::bit_width(U32{0x80000000}) == 32);
  assert(std::bit_floor(U32{3}) == U32{2});
  assert(std::bit_floor(U32{0xFFFFFFFF}) == U32{0x80000000});
  assert(std::bit_ceil(U32{0}) == U32{1});
  assert(std::bit_ceil(U32{3}) == U32{4});
  assert(std::bit_ceil(U32{0x80000000}) == U32{0x80000000});
}

void test_bit_rotation_oracles() {
  constexpr U32 x = 305419896U;
  assert(std::rotl(x, 8) == U32{878082066});
  assert(std::rotr(x, 8) == U32{2014458966});
  assert(std::rotl(x, -8) == U32{2014458966});
  assert(std::rotr(x, -8) == U32{878082066});
  assert(std::rotl(x, 32) == x);
  assert(std::rotr(x, 32) == x);
  assert(std::rotr(std::rotl(x, 7), 7) == x);
  assert(std::rotl(std::rotr(x, 7), 7) == x);
}
