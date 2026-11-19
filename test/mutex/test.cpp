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

void test_unique_lock_move() {
  std::mutex m;
  {
    std::unique_lock<std::mutex> ul1(m);
    std::unique_lock<std::mutex> ul2(std::move(ul1));
  }
}
