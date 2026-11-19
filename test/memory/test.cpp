#include <memory>

struct C{};

template <>
C* std::addressof<C>(C& value) noexcept {
  return std::__addressof(value);
}
