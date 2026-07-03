#include <mutex>

template class std::lock_guard<std::mutex>;
template class std::unique_lock<std::mutex>;
template class std::unique_lock<std::recursive_mutex>;
template class std::scoped_lock<std::mutex, std::mutex>;
