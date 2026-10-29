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

// UNSUPPORTED: c++03
// UNSUPPORTED: no-threads

// <mutex>

// class mutex;

// bool try_lock();

#include "../../custom_mutex.hpp"

#include <cassert>
#include <thread>

#include "make_test_thread.h"

int main(int, char**) {
  // Try to lock a mutex that is not locked yet. This should succeed.
  {
    MyMutex m;
    bool succeeded = m.try_lock();
    assert(succeeded);
    m.unlock();
  }

  // Try to lock a mutex that is already locked. This should fail.
  {
    MyMutex m;
    m.lock();

    std::thread t = support::make_test_thread([&] {
      for (int i = 0; i != 10; ++i) {
        bool succeeded = m.try_lock();
        assert(!succeeded);
      }
    });
    t.join();

    m.unlock();
  }

  return 0;
}
