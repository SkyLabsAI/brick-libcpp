#include <cassert>
#include <mutex>
#include <utility>

using Mutex = std::mutex;
using Lock = std::unique_lock<Mutex>;

bool default_and_observer_oracle() {
  Lock lock;

  return !lock.owns_lock() && !static_cast<bool>(lock) &&
         lock.mutex() == nullptr;
}

bool locking_constructor_oracle() {
  Mutex mutex;
  Lock lock(mutex);

  const bool owning = lock.owns_lock() && static_cast<bool>(lock) &&
                      lock.mutex() == &mutex;
  lock.unlock();
  const bool released = !lock.owns_lock() && !static_cast<bool>(lock) &&
                        lock.mutex() == &mutex;

  return owning && released;
}

bool deferred_transition_oracle() {
  Mutex mutex;
  Lock lock(mutex, std::defer_lock);

  const bool deferred = !lock.owns_lock() && !static_cast<bool>(lock) &&
                        lock.mutex() == &mutex;
  lock.lock();
  const bool acquired = lock.owns_lock() && static_cast<bool>(lock) &&
                        lock.mutex() == &mutex;
  lock.unlock();
  const bool released = !lock.owns_lock() && !static_cast<bool>(lock) &&
                        lock.mutex() == &mutex;

  return deferred && acquired && released;
}

bool move_construction_oracle() {
  Lock empty_source;
  Lock empty_destination(std::move(empty_source));
  const bool empty_transfer =
      !empty_source.owns_lock() && empty_source.mutex() == nullptr &&
      !empty_destination.owns_lock() && empty_destination.mutex() == nullptr;

  Mutex deferred_mutex;
  Lock deferred_source(deferred_mutex, std::defer_lock);
  Lock deferred_destination(std::move(deferred_source));
  const bool deferred_transfer =
      !deferred_source.owns_lock() && deferred_source.mutex() == nullptr &&
      !deferred_destination.owns_lock() &&
      deferred_destination.mutex() == &deferred_mutex;

  Mutex owning_mutex;
  Lock owning_source(owning_mutex);
  Lock owning_destination(std::move(owning_source));
  const bool owning_transfer =
      !owning_source.owns_lock() && owning_source.mutex() == nullptr &&
      owning_destination.owns_lock() &&
      owning_destination.mutex() == &owning_mutex;
  owning_destination.unlock();
  const bool owning_released = !owning_destination.owns_lock() &&
                               owning_destination.mutex() == &owning_mutex;

  return empty_transfer && deferred_transfer && owning_transfer &&
         owning_released;
}

// Dedicated Phase-B selection site for the primary move-assignment contract.
bool move_assignment_primary_oracle() {
  Mutex old_mutex;
  Mutex new_mutex;
  Lock destination(old_mutex);
  Lock source(new_mutex);

  Lock* returned = &(destination = std::move(source));
  const bool transferred =
      returned == &destination && destination.owns_lock() &&
      destination.mutex() == &new_mutex && !source.owns_lock() &&
      source.mutex() == nullptr;

  Lock old_mutex_reacquired(old_mutex);
  const bool prior_destination_released =
      old_mutex_reacquired.owns_lock() &&
      old_mutex_reacquired.mutex() == &old_mutex;
  old_mutex_reacquired.unlock();
  destination.unlock();

  return transferred && prior_destination_released &&
         !destination.owns_lock() && destination.mutex() == &new_mutex;
}

// Same C++ overload, kept separate for Phase-B selection of the alternative
// move-assignment registration.
bool move_assignment_alternative_oracle() {
  Mutex mutex;
  Lock destination;
  Lock source(mutex, std::defer_lock);

  Lock* returned = &(destination = std::move(source));
  const bool deferred_transfer =
      returned == &destination && !destination.owns_lock() &&
      destination.mutex() == &mutex && !source.owns_lock() &&
      source.mutex() == nullptr;

  destination.lock();
  const bool acquired = destination.owns_lock() &&
                        static_cast<bool>(destination) &&
                        destination.mutex() == &mutex;
  destination.unlock();

  return deferred_transfer && acquired && !destination.owns_lock() &&
         destination.mutex() == &mutex;
}

// Dedicated Phase-B selection site for the primary destructor registration.
bool destructor_primary_oracle() {
  Mutex mutex;
  bool empty_state = false;
  bool deferred_state = false;
  bool owning_state = false;

  {
    Lock empty;
    empty_state = !empty.owns_lock() && empty.mutex() == nullptr;
  }
  {
    Lock deferred(mutex, std::defer_lock);
    deferred_state = !deferred.owns_lock() && deferred.mutex() == &mutex;
  }
  {
    Lock owning(mutex);
    owning_state = owning.owns_lock() && owning.mutex() == &mutex;
  }

  Lock reacquired(mutex);
  const bool released = reacquired.owns_lock() &&
                        reacquired.mutex() == &mutex;
  reacquired.unlock();

  return empty_state && deferred_state && owning_state && released;
}

// Same C++ destructor, kept separate for Phase-B selection of the alternative
// application-friendly registration.
bool destructor_alternative_oracle() {
  Mutex mutex;
  bool owning_state = false;
  bool deferred_state = false;
  bool empty_state = false;

  {
    Lock owning(mutex);
    owning_state = owning.owns_lock() && static_cast<bool>(owning) &&
                   owning.mutex() == &mutex;
  }
  {
    Lock deferred(mutex, std::defer_lock);
    deferred_state = !deferred.owns_lock() && !static_cast<bool>(deferred) &&
                     deferred.mutex() == &mutex;
  }
  {
    Lock empty;
    empty_state = !empty.owns_lock() && !static_cast<bool>(empty) &&
                  empty.mutex() == nullptr;
  }

  Lock reacquired(mutex);
  const bool released = reacquired.owns_lock() &&
                        reacquired.mutex() == &mutex;
  reacquired.unlock();

  return owning_state && deferred_state && empty_state && released;
}

bool guarded_composition_oracle() {
  Mutex mutex;
  int protected_value = 0;

  {
    Lock guard(mutex, std::defer_lock);
    if (!guard.owns_lock()) {
      guard.lock();
    }
    if (static_cast<bool>(guard) && guard.mutex() == &mutex) {
      protected_value = 42;
    }
  }

  Lock observer(mutex);
  const bool result = observer.owns_lock() && observer.mutex() == &mutex &&
                      protected_value == 42;
  observer.unlock();
  return result;
}

int main() {
  assert(default_and_observer_oracle());
  assert(locking_constructor_oracle());
  assert(deferred_transition_oracle());
  assert(move_construction_oracle());
  assert(move_assignment_primary_oracle());
  assert(move_assignment_alternative_oracle());
  assert(destructor_primary_oracle());
  assert(destructor_alternative_oracle());
  assert(guarded_composition_oracle());
  return 0;
}
