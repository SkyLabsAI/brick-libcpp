
#include <pthread.h>
#include <cassert>

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
        // Here, it is important that the precondition of `pthread_join` excludes dead-lock because
        // otherwise, we could not retrieve the ownership of the local variable `counter1` when a
        // deadlock is detected. The absence of deadlock is assured by requiring the thread that
        // spawned a thread to also be the one to join it.
        pthread_join(child1, nullptr);
        return;
    }
    pthread_join(child2, nullptr);
    pthread_join(child1, nullptr);
    assert (counter1 == 1);
    assert (counter2 == 3);
}
