
#include <thread>

using namespace std;

class D {};

void thread_1(int &n) {
    n++;
}

void thread_2(int) {
}

void thread_3(int*) {
}

void thread_4(int&&) {
}

void thread_5(D) {
}

void thread_6(D const &) {
}

void thread_7(D const *) {
}

void thread_n(int &n, int, int*, int&&, D, D&, const D&, D&&, D*, D const *) {
    n++;
}

void test1() {
    int n1 = 0;
    int n2 = 1;
    int n3 = 2;
    int m = 0;
    D u, v, w, x, y, z;

    thread child1(thread_1, std::ref(n1));
    thread child2(thread_2, n2);
    thread child3(thread_3, &n3);
    thread child4(thread_4, m);
    thread child5(thread_5, std::ref(x));
    thread child6(thread_6, y);
    thread child7(thread_7, &z);
    child1.join();
    child2.join();
    child3.join();
    child4.join();
    child5.join();
    child6.join();
    child7.join();
}

void test2() {
    int n1 = 0;
    int n2 = 1;
    int n3 = 2;
    int m = 0;
    D u, v, w, x, y, z;
    thread_n(n1, n2, &n3, std::move(m), u, v, w, std::move(x), &y, &z);
    thread childn(thread_n, std::ref(n1), n2, &n3, std::move(m),
                  u, std::ref(v), std::cref(w),
                  std::move(x), &y, const_cast<D const*>(&z));
    childn.join();
}

int main () {
    int n1 = 0;
    int n2 = 1;
    int n3 = 2;
    int m = 0;
    D u, v, w, x, y, z;
    // wrong (because ownership of n1 is given twice)
    // thread child2(thread_2, std::ref(n1), n1, &n1, m);
    // user cast not supported
    // thread_2(std::ref(n1), n2, &n3, std::move(m), x);
    thread childn(thread_n, std::ref(n1), n2, &n3, std::move(m),
                  u, std::ref(v), std::cref(w),
                  std::move(x), &y, const_cast<D const*>(&z));

    thread child1(thread_1, std::ref(n1));
    thread child2(thread_2, n2);
    thread child3(thread_3, &n3);
    thread child4(thread_4, m);
    thread child5(thread_5, x);
    thread child6(thread_6, y);
    thread child7(thread_7, &z);
    child1.join();
    child2.join();
    child3.join();
    child4.join();
    child5.join();
    child6.join();
    child7.join();
}
