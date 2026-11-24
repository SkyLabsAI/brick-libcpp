// SkyLabsAI/brick-libcpp#259: a thread joins a thread that another thread
// created. See join_other_thread_proof.v.
//
// test() creates W, then S, and hands S W's handle through S's argument. S
// joins W. A join that fails (EDEADLK) leaves W running with test()'s local
// [count], so the joiner aborts.
#include <pthread.h>
#include <cstdlib>

void* work(void* arg) {
  ++*static_cast<int*>(arg);
  return nullptr;
}

// Joins the thread whose id [arg] points to.
void* stopper(void* arg) {
  if (pthread_join(*static_cast<pthread_t*>(arg), nullptr))
    abort();
  return nullptr;
}

int test() {
  int count = 0;
  pthread_t w, s;
  if (pthread_create(&w, nullptr, work, &count))
    return 0;
  if (pthread_create(&s, nullptr, stopper, &w)) {
    // No S: the handle for W is still here, so join W directly.
    if (pthread_join(w, nullptr))
      abort();
    return count;
  }
  if (pthread_join(s, nullptr))
    abort();
  return count;
}
