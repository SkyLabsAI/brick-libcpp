/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

// A default mutex initialized statically with PTHREAD_MUTEX_INITIALIZER, used
// without a pthread_mutex_init call.
// https://man7.org/linux/man-pages/man3/pthread_mutex_destroy.3p.html
extern "C" {
pthread_mutex_t static_mutex = PTHREAD_MUTEX_INITIALIZER;

pthread_mutex_t *static_mutex_address()
{
    return &static_mutex;
}

int static_mutex_lock_unlock()
{
    int status = pthread_mutex_lock(&static_mutex);
    if (status != 0)
        return status;
    return pthread_mutex_unlock(&static_mutex);
}
}
