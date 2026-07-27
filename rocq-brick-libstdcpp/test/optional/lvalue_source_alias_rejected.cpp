#include <cassert>
#include <cstdint>
#include <optional>

// Must not be executed by the positive-client oracle. Value construction
// copies the byte into the optional; changing the source cannot change the
// contained byte. A contract that models the contained value as an alias could
// incorrectly prove this assertion.
void lvalue_source_alias_rejected() {
    std::uint8_t source{23};
    const std::optional<std::uint8_t> o{source};

    source = std::uint8_t{91};
    assert(o.has_value() == true);
    assert(static_cast<int>(*o) == 91);
}
