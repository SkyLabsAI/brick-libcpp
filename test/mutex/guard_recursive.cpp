#include <mutex>

void ghost() {}

struct C {
  /*
  Original code:
  std::recursive_mutex m;
  int value{0};
  */

  // This is much easier to verify (avoid strong update for mutex invariant)
  int value{0};
  std::recursive_mutex m;

  void one_answer() {
    std::unique_lock<std::recursive_mutex> lk(m);
    value = 42;
  }

  void inc() {
    std::unique_lock<std::recursive_mutex> lk(m);
    value++;
  }
  void other_answer() {
    std::unique_lock<std::recursive_mutex> lk(m);
    value = 41;
    inc();
  }
};

int test_one_answer2(C& c) {
  std::unique_lock<std::recursive_mutex> lk(c.m);

  c.one_answer();

  return c.value;
}

int test_one_answer() {
  C c;

  std::unique_lock<std::recursive_mutex> lk(c.m);

  c.one_answer();

  return c.value;
}

int test_other_answer() {
  C c;
  c.other_answer();
  return c.value;
}
