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

  // non-recursive; protects m_count and the user resources.
  std::mutex m_lock{};

public:
  // TODO: add the token/given_token accounting, maybe with q*tickets

  void lock() {
    std::thread::id this_id{std::this_thread::get_id()};
    // Open cinv
    if (m_owner != this_id) {
      // here, m_owner is:
      // Some other_thread: ignore for now
      // None: m_count is 0, we don't have exclusive_token.
      // close the invariant, we didn't need to open it

      m_lock.lock();
      // post: here we get the mutex content, count_auth, the m_count field, and exclusive token

      // open cinv again!
      // increment the ghost m_count to 1,
      // set m_owner to Some this_thread
      // set recursive_mutex.owned_count_id_auth from None to Some (this_thread, 0)
      // store the exclusive token
      // close the invariant
      m_owner = this_id;
    } else {
      // here in the else branch, cinv content tells us that:
      // m_owner is Some this_thread, m_count is not zero,
      // so we _observe_ exclusive_token, and we use it to discard the right branch of
      // (this |-> mutex_content γ \\// exclusive_token γ.(excl_gname))

      // and we probably do a ghost m_count increment?
    }
    assert (this_id == m_owner);

    // assert: we own the lock either way!
    if (m_count + 1 == 0) {
      // TODO: review if nontermination is good enough for the paper.
      for (;;);
    }
    m_count++;
  }
  // TODO: connect token and given token to the exclusive token somehow, so that

  void unlock() {
    m_count--;
    if (m_count == 0) {
      m_lock.unlock();
      m_owner = std::thread::id{};
    }
  }
};
