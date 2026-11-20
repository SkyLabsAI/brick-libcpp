/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

void *create_argument_start(void *argument) {
    int *state = (int *)argument;
    *state = 3;
    return argument;
}

int create_argument_result(pthread_t *created, int *state) {
    const int status = pthread_create(created, NULL, create_argument_start, state);
    if (status != 0) {
        return status;
    }
    return 0;
}

#ifdef __cplusplus
}
#endif
