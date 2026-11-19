/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>

// Observe the returned ID against the caller's pre-call logical identity.
extern "C" pthread_t observe_pthread_self(void) {
    return pthread_self();
}
