//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Modified by SkyLabs AI: adapted the mutex type and includes for the
// custom mutex conformance tests. See README.txt and UPSTREAM.json.
//
//===----------------------------------------------------------------------===//

// UNSUPPORTED: no-threads
// UNSUPPORTED: c++03, c++11, c++14

// <shared_mutex>

// class shared_mutex;

// bool try_lock_shared();

#include "../../../shared_mutex/custom_shared_mutex.hpp"

#include <cassert>
#include <thread>
#include <vector>

#include "make_test_thread.h"

int main(int, char**) {
  // Try to lock-shared a mutex that is not locked yet. This should succeed.
  {
    MySharedMutex m;
    std::vector<std::thread> threads;
    for (int i = 0; i != 5; ++i) {
      threads.push_back(support::make_test_thread([&] {
        bool succeeded = m.try_lock_shared();
        assert(succeeded);
        m.unlock_shared();
      }));
    }

    for (auto& t : threads)
      t.join();
  }

  // Try to lock-shared a mutex that is already exclusively locked. This should fail.
  {
    MySharedMutex m;
    m.lock();

    std::vector<std::thread> threads;
    for (int i = 0; i != 5; ++i) {
      threads.push_back(support::make_test_thread([&] {
        bool succeeded = m.try_lock_shared();
        assert(!succeeded);
      }));
    }

    for (auto& t : threads)
      t.join();

    m.unlock();
  }

  // Try to lock-shared a mutex that is already lock-shared. This should succeed.
  {
    MySharedMutex m;
    m.lock_shared();
    std::vector<std::thread> threads;
    for (int i = 0; i != 5; ++i) {
      threads.push_back(support::make_test_thread([&] {
        bool succeeded = m.try_lock_shared();
        assert(succeeded);
        m.unlock_shared();
      }));
    }
    m.unlock_shared();

    for (auto& t : threads)
      t.join();
  }

  return 0;
}
