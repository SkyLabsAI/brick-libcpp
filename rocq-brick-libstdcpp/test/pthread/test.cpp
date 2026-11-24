
#include <pthread.h>
#include <cassert>
#include <cstdlib>

void* thread_fn(void* data) {
    int* counter = static_cast<int*>(data);
    ++*counter;
    return nullptr;
}

void multithreaded_broken () {
    int counter = 0;
    int err;
    pthread_t child;

    if (pthread_create(&child, nullptr, thread_fn, &counter) != 0)
        return;
    counter++; // problem here
    pthread_join(child, nullptr);
}

void* cancelable_thread(void* data) {
    int* counter = static_cast<int*>(data);
    ++*counter;
    pthread_testcancel();
    ++*counter;
    pthread_testcancel();
    ++*counter;
    return nullptr;
}

void multithreaded_ok () {
    int counter1 = 0;
    int counter2 = 0;
    int err;
    pthread_t child1, child2;

    if (pthread_create(&child1, nullptr, thread_fn, &counter1) != 0)
        return;
    if (pthread_create(&child2, nullptr, cancelable_thread, &counter2) != 0) {
        // A failed join (EDEADLK) leaves `child1` running with `counter1`, so returning would
        // free a local that the thread still uses: abort instead.
        if (pthread_join(child1, nullptr) != 0)
            abort();
        return;
    }
    if (pthread_join(child2, nullptr) != 0)
        abort();
    if (pthread_join(child1, nullptr) != 0)
        abort();
    assert (counter1 == 1);
    assert (counter2 == 3);
}
