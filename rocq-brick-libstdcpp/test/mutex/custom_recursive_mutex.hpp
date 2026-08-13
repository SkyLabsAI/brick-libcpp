#include <atomic>
#include <mutex>
#include <thread>
#include <cassert>

#pragma once
class MyRecursiveMutex {
  // not protected by the lock, but atomic
  std::atomic<std::thread::id> owner{};

  // protected by the lock
  unsigned long long count{0};

  // non-recursive; protects count and the user resources.
  std::mutex i_lock{};

public:
  void lock() {
    std::thread::id this_id{std::this_thread::get_id()};
    if (this->owner != this_id) {
      i_lock.lock();
      this->owner = this_id;
    }
    assert (this_id == this->owner);

    // assert: we own the lock either way!
    if (count + 1 == 0) {
      // TODO: review if nontermination is good enough for the paper.
      for (;;);
    }
    count++;
  }

  void unlock() {
    count--;
    if (count == 0) {
      i_lock.unlock();
      owner = std::thread::id{};
    }
  }
};
