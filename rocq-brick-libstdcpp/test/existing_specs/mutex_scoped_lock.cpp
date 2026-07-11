#include <cassert>
#include <mutex>

void test_two_mutex_lifecycle() {
    int left = 3;
    int right = 5;
    std::mutex first;
    std::mutex second;

    {
        std::scoped_lock<std::mutex, std::mutex> guard(first, second);

        assert(left == 3);
        assert(right == 5);

        ++left;
        --right;
        assert(left == 4);
        assert(right == 4);

        --left;
        ++right;
    }
}

void test_reacquire_after_scope() {
    int left = 13;
    int right = 21;
    std::mutex first;
    std::mutex second;

    {
        std::scoped_lock<std::mutex, std::mutex> guard(first, second);
        assert(left == 13);
        assert(right == 21);
    }

    {
        std::scoped_lock<std::mutex, std::mutex> guard(second, first);

        left += right;
        assert(left == 34);
        left -= right;

        right += left;
        assert(right == 34);
        right -= left;
    }
}

int main() {
    test_two_mutex_lifecycle();
    test_reacquire_after_scope();
    return 0;
}
