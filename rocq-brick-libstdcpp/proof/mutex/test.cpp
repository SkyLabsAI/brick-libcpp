#include "inc.hpp"

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
