/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * SPDX-License-Identifier: BSD-3-Clause
 */
#pragma once
#include <atomic>

/*
A spinlock behind the C calling convention of glibc's default pthread mutex.

This is the pthread counterpart of ../mutex/custom_mutex.hpp. Its lock, unlock
and trylock functions are verified against the same pthread_mutex_spec
contracts as glibc's pthread_mutex_lock, pthread_mutex_unlock and
pthread_mutex_trylock:
- they take the mutex by pointer and return 0 on success;
- my_mutex_trylock returns EBUSY while the mutex is held, including for its
  owner, and succeeds on an uncontended mutex;
- my_mutex_lock by the owner spins forever.

Its lifetime is that of a C++ object: the constructor and destructor play the
roles of pthread_mutex_init and pthread_mutex_destroy, with the contracts that
std::mutex uses. Unlike MyMutex, it does not record its owner: the contracts
track ownership in ghost state only.
*/

#define MY_EBUSY 16 /* EBUSY on Linux */

struct my_mutex_t {
  std::atomic<int> m_lock{0};

  my_mutex_t() noexcept {}
  ~my_mutex_t() {}
};

inline int my_mutex_lock(my_mutex_t *m) {
  while (m->m_lock.exchange(1)) {
  }
  return 0;
}

inline int my_mutex_trylock(my_mutex_t *m) {
  if (m->m_lock.exchange(1))
    return MY_EBUSY;
  return 0;
}

inline int my_mutex_unlock(my_mutex_t *m) {
  m->m_lock.store(0);
  return 0;
}
