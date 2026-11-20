// Two threads join each other although each holds a [pthread.handle] whose
// spawner is its own current thread. See join_reuse_cycle.md.
//
// test() starts S. S records its own std::thread::id and starts X. test()
// joins S, which frees S's thread id, and then publishes S's handle for X
// through [st]. X takes it and starts Y, which can reuse S's id. If it does,
// Y passes the handle's spawner check and joins X while X joins Y.
//
// A join that fails sets [failed], and test() returns only after reading it.
// The specs say pthread_join always returns 0, so the proof shows that test()
// never returns. A pthread_join that detects the cycle, which POSIX allows,
// makes test() return.
//
// The code avoids built-in assignments and comparisons: auto's rules for those
// rest on an unsound evaluation-order axiom.
#include <pthread.h>
#include <cstdio>
#include <thread>

struct Shared {
  int st = 0;          // atomic; 1 while S's handle for X is published
  int failed = 0;      // atomic; 1 once a join failed
  std::thread::id id0; // S's id
  pthread_t x;         // X's id
};

int take_st(Shared* sh) {
  return __atomic_exchange_n(&sh->st, 0, __ATOMIC_SEQ_CST);
}

void publish(Shared* sh) { __atomic_store_n(&sh->st, 1, __ATOMIC_SEQ_CST); }

int load_failed(Shared* sh) {
  return __atomic_load_n(&sh->failed, __ATOMIC_SEQ_CST);
}

void set_failed(Shared* sh) {
  __atomic_store_n(&sh->failed, 1, __ATOMIC_SEQ_CST);
}

void* y_fn(void* arg) {
  Shared* sh = static_cast<Shared*>(arg);
  if (std::this_thread::get_id() == sh->id0) {
    if (pthread_join(sh->x, nullptr))
      set_failed(sh);
  }
  return nullptr;
}

void* x_fn(void* arg) {
  Shared* sh = static_cast<Shared*>(arg);
  while (!take_st(sh)) {
  }
  pthread_t y;
  if (!pthread_create(&y, nullptr, y_fn, sh)) {
    if (pthread_join(y, nullptr))
      set_failed(sh);
  }
  return nullptr;
}

void* s_fn(void* arg) {
  Shared* sh = static_cast<Shared*>(arg);
  sh->id0 = std::this_thread::get_id();
  if (pthread_create(&sh->x, nullptr, x_fn, sh)) {
    // X does not exist, so there is nothing to publish.
    while (!load_failed(sh)) {
    }
  }
  return nullptr;
}

void test() {
  Shared sh;
  pthread_t s;
  if (!pthread_create(&s, nullptr, s_fn, &sh)) {
    pthread_join(s, nullptr);
    publish(&sh);
  }
  while (!load_failed(&sh)) {
  }
}

int main() {
  test();
  std::puts("REACHED_END_OF_TEST");
  return 0;
}
