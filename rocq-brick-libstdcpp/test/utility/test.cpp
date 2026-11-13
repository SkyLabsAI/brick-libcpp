#include <utility>

struct foo {};

void test_move() {
  foo f;
  std::move(f);
  std::move<foo&>(f);
  // Fails
  // std::move<foo>(f);
  // std::move<foo&&>(f);
  std::move(1);
  int i = 2;
  std::move(i);

  // Non-idiomatic uses of forward for testing

  // lvalue references
  std::forward<const foo &>(f);
  // Fails!
  // std::forward<const foo &>(std::move(f));

  // rvalue references
  std::forward<foo>(f);
  std::forward<foo>(std::move(f));

  // rvalue references, redux.
  // Never used in real code
  std::forward<foo&&>(f);
  std::forward<foo&&>(std::move(f));

  // primitives
  std::forward<const int &>(i);
  std::forward<int>(i);
  std::forward<int>(std::move(i));

  std::forward<int&&>(i);
  std::forward<int&&>(std::move(i));
}
