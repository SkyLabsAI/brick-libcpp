#include <mutex>

struct C {
  std::recursive_mutex m;
  int value{0};

  void one_answer() {
    std::unique_lock<std::recursive_mutex> lk(m);
    value = 42;
  }

  void inc() {
    std::unique_lock<std::recursive_mutex> lk(m);
    value = 42;
  }
  void other_answer() {
    std::unique_lock<std::recursive_mutex> lk(m);
    value = 41;
    inc();
  }
};

int test_one_answer() {
  C c;
  c.one_answer();
  return c.value;
}

int test_other_answer() {
  C c;
  c.other_answer();
  return c.value;
}
