/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

bool compare_same(pthread_t id) {
    return pthread_equal(id, id) != 0;
}

bool compare_distinct(pthread_t first, pthread_t second) {
    return pthread_equal(first, second) == 0;
}
