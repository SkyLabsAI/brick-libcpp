#include <mutex>
#include <shared_mutex>

void test_shared_mutex() {
  std::shared_mutex m;

  m.lock();
  m.unlock();
}

void test_shared_mutex_shared() {
  std::shared_mutex m;

  m.lock_shared();
  m.unlock_shared();
}

// Unique_lock tests:

void test_unique_lock() {
  std::shared_mutex m;
  {
    std::unique_lock<std::shared_mutex> ul(m);
  }
}

void test_unique_lock_defer() {
  std::shared_mutex m;
  {
    std::unique_lock<std::shared_mutex> ul(m, std::defer_lock);
  }
}

void test_unique_lock_move() {
  std::shared_mutex m;
  {
    std::unique_lock<std::shared_mutex> ul1(m);
    std::unique_lock<std::shared_mutex> ul2(std::move(ul1));
  }
}

// Possible fancier tests.

bool resource = false;

void test_shared_mutex_fancy() {
  std::shared_mutex m;
  // TODO: move to unique_lock here
  m.lock();
  resource = true;
  m.unlock();
}

void test_shared_mutex_shared_fancy() {
  std::shared_mutex m;

  for (;;) {
    // TODO: move to unique_lock here
    m.lock_shared();
    // XXX: Here, we only show that it's safe to _read_ from the shared resource after lock_shared.
    // We do _not_ show that we can grab a read lock from 2 threads in parallel
    // _but_ that's a liveness property.
    bool ret = resource;
    m.unlock_shared();

    if (ret)
      break;
  }
}
