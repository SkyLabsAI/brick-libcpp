#pragma once
#include <atomic>
#include <climits>

// Figure 11 of papers/cpp-mutex/stdcpp.pdf, packaged as a class.
// The saturation check avoids signed overflow in the CAS argument val + 1.
class MySharedMutex {
  std::atomic<int> sharers{0};

public:
  MySharedMutex() {}
  ~MySharedMutex() {}

  void lock() {
    int idle = 0;
    while (!sharers.compare_exchange_strong(idle, -1))
      { idle = 0; }
  }

  void unlock() {
    sharers = 0;
  }

  void lock_shared() {
    int val;
    do { val = sharers; }
    // wait if val=-1 (writer-locked) or val=INT_MAX (so to avoid overflow)
    while (val < 0 || val == INT_MAX ||
           !sharers.compare_exchange_strong(val, val + 1));
  }

  void unlock_shared() {
    sharers--;
  }
};
