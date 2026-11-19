/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

// Observe the actual status of the call. The client contract also observes
// acquisition through the owner-specific held capability and protected resource.
int lock_live(pthread_mutex_t *mutex)
{
    return pthread_mutex_lock(mutex);
}
