#include <atomic>
#include <mutex>
#include <thread>
#include <cassert>

#pragma once
class MyRecursiveMutex {
  // not protected by the lock, but atomic
  std::atomic<std::thread::id> m_owner{};

  // protected by the lock
  unsigned long long m_count{0};

  // non-recursive; protects count and the user resources.
  std::mutex m_lock{};

public:
  void lock() {
    std::thread::id this_id{std::this_thread::get_id()};
    if (m_owner != this_id) {
      m_lock.lock();
      this->m_owner = this_id;
    }
    assert (this_id == m_owner);

    // assert: we own the lock either way!
    if (m_count + 1 == 0) {
      // TODO: review if nontermination is good enough for the paper.
      for (;;);
    }
    m_count++;
  }

  void unlock() {
    m_count--;
    if (m_count == 0) {
      m_lock.unlock();
      m_owner = std::thread::id{};
    }
  }
};
