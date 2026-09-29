#include <cstdio>
#include <mutex>

// [R g] says that the account's balance is protected by namespace g.
class C {
private:
  unsigned long balance;
  std::recursive_mutex mut; // protects balance

public:
  explicit C(unsigned long initial_balance) : balance(initial_balance) {}

  template <typename F>

  // [| g \subset E |]
  // c |-> R g ** my_mutexes th E
  // { c,,balance |-> v0 } f {\exists v', c,,balance |-> v' }
  void call(F f) {
    std::lock_guard<std::recursive_mutex> lg(mut);
    // c,,balance |-> v0
    f(balance);
    // c,,balance |-> v'
    //~lock_guard()
    // c |-> R g ** my_mutexes th E
  }

  void print_balance() {
    std::lock_guard<std::recursive_mutex> lg(mut);
    std::printf("Balance: %lu\n", balance);
  }
};


void transfer_seq(unsigned long& b1, unsigned long& b2, unsigned long i) {
  b1 -= i;
  b2 += i;
}

// from |-> R g1 ** to |-> R g2 ** my_mutexes th E
void transfer(C& from, C& to, unsigned long i) {
  from.call([&](unsigned long& from_balance) {
    // from ,, balance |-> v1
    // ** to |-> R g2
    // ** my_mutexes th E\g1
    to.call([&](unsigned long& to_balance) {
      // from ,, balance |-> v1
      // ** to ,, balance |-> v2
      // ** my_mutexes th (E\g1)\g2
      transfer_seq(from_balance, to_balance, i);
      // from ,, balance |-> v1-i
      // ** to ,, balance |-> v2+i
      // ** my_mutexes th (E\g1)\g2
    });
  });
}

int main() {
  C from{4};
  C to{2};
  transfer(from, to, 3);
  return 0;
}
