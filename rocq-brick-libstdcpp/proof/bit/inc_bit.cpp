#include <bit>
#include <cstdint>

// Materialize only the concrete unsigned-int specialization used by clients.
template int std::popcount<unsigned int>(unsigned int) noexcept;
template int std::countl_zero<unsigned int>(unsigned int) noexcept;
template int std::countr_zero<unsigned int>(unsigned int) noexcept;
template int std::countl_one<unsigned int>(unsigned int) noexcept;
template int std::countr_one<unsigned int>(unsigned int) noexcept;
template unsigned int std::bit_width<unsigned int>(unsigned int) noexcept;
template unsigned int std::bit_ceil<unsigned int>(unsigned int) noexcept;
template unsigned int std::bit_floor<unsigned int>(unsigned int) noexcept;
template bool std::has_single_bit<unsigned int>(unsigned int) noexcept;
template unsigned int std::rotl<unsigned int>(unsigned int, int) noexcept;
template unsigned int std::rotr<unsigned int>(unsigned int, int) noexcept;
