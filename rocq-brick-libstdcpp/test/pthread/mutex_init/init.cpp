/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <stddef.h>
#include <pthread.h>

extern "C" int init_default_mutex(pthread_mutex_t *mutex)
{
    return pthread_mutex_init(mutex, NULL);
}
