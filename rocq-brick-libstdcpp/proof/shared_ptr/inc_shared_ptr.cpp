#include <memory>
#include <limits>
#include <type_traits>

// specs.v reserves one piece index per representable positive strong count.
// Check the libstdc++ ABI rather than inferring this bound from pointer size.
static_assert(std::is_same_v<_Atomic_word, int>);
static_assert(std::numeric_limits<_Atomic_word>::max() == 2147483647);
