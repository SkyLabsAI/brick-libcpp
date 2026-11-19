/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <errno.h>
#include <pthread.h>

// Observe the result when the caller has the full access loan. The full
// loan rules out an existing holder and another outstanding access loan.
bool trylock_uncontended(pthread_mutex_t *mutex) {
    return pthread_mutex_trylock(mutex) == 0;
}

// Observe the result when the calling thread already holds this default
// mutex. The caller retains its held right and the protected resource.
bool trylock_current_owner(pthread_mutex_t *mutex) {
    return pthread_mutex_trylock(mutex) == EBUSY;
}

// Observe the result during a stable peer hold. The logical peer witness
// stays live across the call, while this caller keeps its separate loan.
bool trylock_peer_contention(pthread_mutex_t *mutex) {
    return pthread_mutex_trylock(mutex) == EBUSY;
}
