/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

// The caller owns the live default mutex. The client observes the result
// directly and checks the returned access capability in its Rocq postcondition.
int unlock_owned_mutex(pthread_mutex_t *mutex)
{
    return pthread_mutex_unlock(mutex);
}
