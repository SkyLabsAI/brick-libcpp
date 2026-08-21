#include <atomic>
#include <thread>
#include <cassert>

#pragma once
/*
A mutex, implemented via a spinlock.

We subset the std::mutex interface: we omit methods, but the ones we implement
have the same spec.

We store who holds the lock, and check that it evolves according to the
std::mutex protocol:
- can't attempt to lock recursively
- can only be unlocked by whichever thread locked it.
- can't be destroyed while held.
*/
class MyMutex {
  std::atomic<bool> m_lock{false};

  std::thread::id m_owner{};

  // "Actual locking"
  void do_lock() {
    while (m_lock.exchange(true)) {
      std::this_thread::yield();
    }
  }

  void do_unlock() {
    m_lock = false;
  }
public:

  void lock() {
    std::thread::id this_id{std::this_thread::get_id()};
    assert(m_owner != this_id); // benign race. UB?

    do_lock(); // start of critical section

    m_owner = this_id;
  }

  void unlock(){
    assert(m_owner == std::this_thread::get_id());
    m_owner = std::thread::id(); // unowned

    do_unlock(); // end of critical section
  }

  ~MyMutex() {
    assert(!m_lock);
    assert(m_owner == std::thread::id()); //unowned
  }
};
