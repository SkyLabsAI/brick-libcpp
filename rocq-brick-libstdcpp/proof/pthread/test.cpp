
#include <pthread.h>
#include <assert.h>

void* thread_fn(void* data) {
    int* counter = static_cast<int*>(data);
    ++*counter;
    return nullptr;
}

void multithreaded_broken () {
    int counter = 0;
    int err;
    void *result;
    pthread_attr_t attr;
    pthread_t child;

    pthread_attr_init(&attr);
    if (pthread_create(&child, &attr, thread_fn, &counter) != 0)
        return;
    counter++; // problem here
    pthread_join(child, &result);
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

// This function is meant to encapsulate an unsound use of void pointer and can't be verified.
bool is_canceled(void** result) {
    return *result == PTHREAD_CANCELED; // this is not a valid use of pointers.
}

void multithreaded_ok () {
    int counter1 = 0;
    int counter2 = 0;
    int err;
    void *result;
    pthread_attr_t attr;
    pthread_t child1, child2;
    pthread_attr_init(&attr);

    if (pthread_create(&child1, &attr, thread_fn, &counter1) != 0)
        return;
    if (pthread_create(&child2, &attr, cancelable_thread, &counter2) != 0) {
        pthread_join(child1, &result);
        return;
    }
    pthread_cancel(child2);
    pthread_join(child2, &result);
    if (is_canceled(&result)) {
        assert (0 < counter2 && counter2 <= 2);
    } else {
        assert (counter2 == 3);
    }
    pthread_join(child1, &result);
    assert (counter1 == 1);
}
