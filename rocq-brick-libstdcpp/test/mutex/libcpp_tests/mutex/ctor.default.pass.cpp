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

// <mutex>

// class mutex;

// mutex() noexcept;

#include "../../custom_mutex.hpp"

#include <cassert>
#include <type_traits>

static_assert(std::is_nothrow_default_constructible<MyMutex>::value, "");

int main(int, char**) {
  // The mutex is unlocked after default construction
  {
    MyMutex m;
    assert(m.try_lock());
    m.unlock();
  }

  return 0;
}
