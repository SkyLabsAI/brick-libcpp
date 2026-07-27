#include <cassert>
#include <cstdint>
#include <optional>

// Must not be executed: dereferencing an empty optional is undefined behavior
// in C++20. A sound contract must not prove the asserted concrete byte.
void empty_deref_max_rejected() {
    const std::optional<std::uint8_t> o{std::nullopt};
    assert(static_cast<int>(*o) == 255);
}
