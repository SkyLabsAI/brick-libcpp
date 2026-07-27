#include <cstdint>
#include <optional>

// Must not be executed: even when the result is discarded, invoking
// operator*() on an empty optional violates its C++20 precondition. This probe
// attacks call definedness rather than guessing a concrete result.
void empty_deref_discarded_rejected() {
    const std::optional<std::uint8_t> o{std::nullopt};
    static_cast<void>(*o);
}
