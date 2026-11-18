// Copyright (c) 2026 SkyLabs AI, Inc.
// SPDX-License-Identifier: BSD-3-Clause
#include <pthread.h>
#include <cassert>
#include <cerrno>

int read_locked(pthread_mutex_t* mutex, int* value) {
    pthread_mutex_lock(mutex);
    int result = *value;
    pthread_mutex_unlock(mutex);
    return result;
}

bool try_read(pthread_mutex_t* mutex, int* value, int* result) {
    if (pthread_mutex_trylock(mutex) != 0)
        return false;
    *result = *value;
    pthread_mutex_unlock(mutex);
    return true;
}

// These clients deliberately ignore the return codes of lock and unlock.
// Their proof preconditions restrict them to the supported glibc default case.
void increment_locked(pthread_mutex_t* mutex, int* value) {
    pthread_mutex_lock(mutex);
    ++*value;
    pthread_mutex_unlock(mutex);
}

bool try_increment(pthread_mutex_t* mutex, int* value) {
    if (pthread_mutex_trylock(mutex) != 0)
        return false;
    ++*value;
    pthread_mutex_unlock(mutex);
    return true;
}

int try_while_owned(pthread_mutex_t* mutex) {
    return pthread_mutex_trylock(mutex);
}

int try_when_held(pthread_mutex_t* mutex) {
    return pthread_mutex_trylock(mutex);
}

int try_when_free(pthread_mutex_t* mutex) {
    return pthread_mutex_trylock(mutex);
}

// Under the already-owned precondition this has no normal return. The native
// tests must not execute it: a NORMAL mutex deadlocks on same-thread relocking.
void relock_while_owned(pthread_mutex_t* mutex) {
    pthread_mutex_lock(mutex);
}

void initialize_default(pthread_mutex_t* mutex) {
    pthread_mutex_init(mutex, nullptr);
}

void destroy_default(pthread_mutex_t* mutex) {
    pthread_mutex_destroy(mutex);
}

bool self_equal() {
    return pthread_equal(pthread_self(), pthread_self()) != 0;
}

bool self_is_zero() {
    return pthread_equal(pthread_self(), 0) != 0;
}

pthread_mutex_t static_mutex = PTHREAD_MUTEX_INITIALIZER;
// This initialization route is specific to the supported glibc ABI.
pthread_mutex_t zero_mutex;

int read_static_then_destroy(int* value) {
    int result = read_locked(&static_mutex, value);
    pthread_mutex_destroy(&static_mutex);
    return result;
}

int read_zero_then_destroy(int* value) {
    int result = read_locked(&zero_mutex, value);
    pthread_mutex_destroy(&zero_mutex);
    return result;
}

#ifdef PTHREAD_MUTEX_NATIVE_TEST
void remember_owner(pthread_mutex_t*, unsigned long*);
void clear_owner_and_unlock(pthread_mutex_t*, unsigned long*);
bool owner_is_self(const unsigned long*);
bool resume_owned(pthread_mutex_t*, unsigned long*);

struct contention_data {
    pthread_mutex_t* mutex;
    int* value;
    bool acquired;
    int error;
    unsigned long* owner;
};

static void* try_from_another_thread(void* raw) {
    auto* data = static_cast<contention_data*>(raw);
    data->error = pthread_mutex_trylock(data->mutex);
    if (data->error == 0)
        pthread_mutex_unlock(data->mutex);
    remember_owner(data->mutex, data->owner);
    data->acquired = try_increment(data->mutex, data->value);
    return nullptr;
}

static void check_default(pthread_mutex_t* mutex) {
    unsigned long owner = 0;
    remember_owner(mutex, &owner);
    assert(owner_is_self(&owner));
    assert(resume_owned(mutex, &owner));
    clear_owner_and_unlock(mutex, &owner);
    assert(owner == 0);
    int value = 0;
    increment_locked(mutex, &value);
    assert(value == 1);
    assert(try_increment(mutex, &value));
    assert(value == 2);
    assert(pthread_mutex_lock(mutex) == 0);
    assert(try_while_owned(mutex) == EBUSY);
    contention_data data{mutex, &value, true, 0, &owner};
    pthread_t child;
    assert(pthread_create(&child, nullptr, try_from_another_thread, &data) == 0);
    assert(pthread_join(child, nullptr) == 0);
    assert(!data.acquired);
    assert(data.error == EBUSY);
    assert(owner == 0); // Failed trylock does not write the owner word.
    assert(value == 2);
    assert(pthread_mutex_unlock(mutex) == 0);
    assert(try_increment(mutex, &value));
    assert(value == 3);
    assert(pthread_mutex_destroy(mutex) == 0);
}

int main() {
    assert(self_equal());
    assert(!self_is_zero());
    check_default(&static_mutex);
    check_default(&zero_mutex);
    pthread_mutex_t dynamic_mutex;
    assert(pthread_mutex_init(&dynamic_mutex, nullptr) == 0);
    check_default(&dynamic_mutex);
}
#endif
