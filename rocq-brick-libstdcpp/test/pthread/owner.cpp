// Copyright (c) 2026 SkyLabs AI, Inc. SPDX-License-Identifier: BSD-3-Clause
#include <pthread.h>

// A trylock wrapper records the owner only after successful acquisition.
void remember_owner(pthread_mutex_t* mutex, unsigned long* owner) {
    if (pthread_mutex_trylock(mutex) == 0)
        *owner = pthread_self();
}

void clear_owner_and_unlock(pthread_mutex_t* mutex, unsigned long* owner) {
    *owner = 0;
    pthread_mutex_unlock(mutex);
}

bool owner_is_self(const unsigned long* owner) {
    return pthread_equal(pthread_self(), *owner) != 0;
}

// Re-entering a state machine that already holds its mutex relies on EBUSY
// preserving both the held token and the recorded owner.
bool resume_owned(pthread_mutex_t* mutex, unsigned long* owner) {
    remember_owner(mutex, owner);
    return owner_is_self(owner);
}
