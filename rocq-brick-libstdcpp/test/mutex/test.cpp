#include <mutex>

using namespace std;

void test_mutex() {
  std::mutex m;
  m.lock();
  m.unlock();
}

void test_lock_guard() {
  std::mutex m;
  {
    std::lock_guard<std::mutex> lm(m);
  }
}

void test_scoped_lock() {
  std::mutex m1, m2;
  std::scoped_lock lock(m1, m2);
}
