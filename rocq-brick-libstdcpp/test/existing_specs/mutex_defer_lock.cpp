#include <cassert>
#include <mutex>

void test_copy_lifecycle() {
    std::defer_lock_t source(std::defer_lock);
    std::defer_lock_t copy(source);
}

void test_source_survives_inner_copy() {
    std::defer_lock_t source(std::defer_lock);
    {
        std::defer_lock_t inner(source);
    }
    std::defer_lock_t later(source);
}

void test_unique_lock_with_copied_defer_tag() {
    std::mutex mutex;
    std::defer_lock_t source(std::defer_lock);
    std::defer_lock_t copy(source);
    std::unique_lock<std::mutex> lock(mutex, copy);

    assert(!lock.owns_lock());
}

int main() {
    test_copy_lifecycle();
    test_source_survives_inner_copy();
    test_unique_lock_with_copied_defer_tag();
    return 0;
}
