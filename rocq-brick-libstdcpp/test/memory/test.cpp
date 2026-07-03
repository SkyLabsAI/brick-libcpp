#include <memory>

struct C{};
template C* std::addressof<C>(C&);
