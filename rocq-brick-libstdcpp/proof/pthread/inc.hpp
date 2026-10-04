/*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#include <pthread.h>
#include <errno.h>

enum pthread_errno : int {
    CANCELED = -1, // same as PTHREAD_CANCELED but it is not a valid way to define an enum,
};
