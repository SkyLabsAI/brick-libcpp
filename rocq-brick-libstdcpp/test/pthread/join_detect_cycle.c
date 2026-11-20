/* A pthread_join that reports EDEADLK for self-joins and for two threads
 * joining each other, then defers to the C library's pthread_join.
 *
 * POSIX lets pthread_join fail with EDEADLK when "a deadlock was detected";
 * this wrapper is one such implementation. Load it with LD_PRELOAD.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <pthread.h>

#define MAX_JOINS 64

static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static struct {
  int used;
  pthread_t joiner, target;
} joins[MAX_JOINS];

int pthread_join(pthread_t target, void **ret) {
  static int (*real_join)(pthread_t, void **);
  if (!real_join)
    real_join = (int (*)(pthread_t, void **))dlsym(RTLD_NEXT, "pthread_join");

  pthread_t self = pthread_self();
  if (pthread_equal(target, self))
    return EDEADLK;

  /* Checking for the reverse join and registering this one happen under one
   * lock, so of two threads joining each other the second always sees the
   * first. */
  pthread_mutex_lock(&mu);
  int slot = -1;
  for (int i = 0; i < MAX_JOINS; i++) {
    if (joins[i].used && pthread_equal(joins[i].joiner, target) &&
        pthread_equal(joins[i].target, self)) {
      pthread_mutex_unlock(&mu);
      return EDEADLK;
    }
    if (!joins[i].used && slot < 0)
      slot = i;
  }
  if (slot >= 0) {
    joins[slot].used = 1;
    joins[slot].joiner = self;
    joins[slot].target = target;
  }
  pthread_mutex_unlock(&mu);

  int r = real_join(target, ret);

  if (slot >= 0) {
    pthread_mutex_lock(&mu);
    joins[slot].used = 0;
    pthread_mutex_unlock(&mu);
  }
  return r;
}
