/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <pthread.h>
#include <stddef.h>

struct join_message {
    pthread_t target;
    bool store_result;
    bool joined_target;
};

extern "C" int join_creator(pthread_t target, void **slot)
{
    return pthread_join(target, slot);
}

extern "C" void *join_peer_start(void *argument)
{
    join_message *message = static_cast<join_message *>(argument);
    if (pthread_self() == message->target) {
        message->joined_target = false;
        return NULL;
    }

    void *result = NULL;
    if (message->store_result) {
        result = argument;
        pthread_join(message->target, &result);
    } else {
        pthread_join(message->target, NULL);
    }
    message->joined_target = true;
    return result;
}

extern "C" int create_then_join_via_peer(join_message *message,
                                                pthread_t *peer,
                                                void **peer_result,
                                                void *(*worker_start)(void *),
                                                void *worker_argument)
{
    const int worker_status =
        pthread_create(&message->target, NULL, worker_start, worker_argument);
    if (worker_status != 0)
        return worker_status;

    const int peer_status =
        pthread_create(peer, NULL, join_peer_start, message);
    if (peer_status != 0) {
        pthread_join(message->target, NULL);
        return peer_status;
    }

    const int join_status = pthread_join(*peer, peer_result);
    return message->joined_target ? join_status : -1;
}
