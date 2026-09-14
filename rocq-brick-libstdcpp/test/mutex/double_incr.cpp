#include <cassert>
#include <mutex>
#include <thread>

unsigned int x = 0;
std::mutex m;

void double_incr() {
  m.lock();
  x++;
  x++;
  m.unlock();
}

int main() {
  std::thread t1(double_incr);
  std::thread t2(double_incr);

  t1.join();
  t2.join();

  assert(x == 4);
  return 0;
}
