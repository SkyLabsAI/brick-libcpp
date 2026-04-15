#include <mutex>

template class std::lock_guard<std::mutex>;
template class std::unique_lock<std::mutex>;
template class std::scoped_lock<std::mutex, std::mutex>;

inline void foo() {
  std::mutex m1, m2;
  std::scoped_lock lock(m1, m2);
}
