/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

// Translation fixture for the C-linkage API. These functions are never executed.
extern "C" int join_discard_shape(pthread_t id) {
    return pthread_join(id, nullptr);
}

extern "C" int join_store_shape(pthread_t id, void **slot) {
    return pthread_join(id, slot);
}
