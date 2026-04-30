#include <mutex>

using namespace std;

void test() {
  std::mutex m;
  m.lock();
  m.unlock();
}

void test2() {
  std::mutex m;
  {
    std::lock_guard<std::mutex> lm(m);
  }
}

void test_unique_lock() {
  std::mutex m;
  {
    std::unique_lock<std::mutex> ul(m);
  }
}

void test_unique_lock_defer() {
  std::mutex m;
  {
    std::unique_lock<std::mutex> ul(m, std::defer_lock);
  }
}
