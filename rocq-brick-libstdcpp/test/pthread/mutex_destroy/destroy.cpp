/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

// The caller provides a live, unlocked default mutex with no concurrent uses.
// Return the exact destroy result so a caller can distinguish success.
int destroy_default_mutex(pthread_mutex_t *mutex)
{
    return pthread_mutex_destroy(mutex);
}
