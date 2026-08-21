#include <atomic>
#include <thread>
#include <cassert>

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
  std::atomic<bool> m_lock;

  std::thread::id m_owner{};

  void assert_owner(std::thread::id id) {
    assert(m_owner == id);
  }
  void set_owner(std::thread::id id) {
    m_owner = id;
  }

public:

  void lock() {
    std::thread::id this_id{std::this_thread::get_id()};

    assert(m_owner != this_id);

    bool old;
    while (old = false, !m_lock.compare_exchange_strong(old, true)) {}

    m_owner = this_id;
  }

  void unlock(){
    assert(m_owner == std::this_thread::get_id());

    m_lock = false;

    m_owner = std::thread::id(); // unowned
  }

  ~MyMutex() {
    assert(m_owner == std::thread::id()); //unowned
  }
};
