(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.mutex.pred.
Require Export skylabs.brick.libstdcpp.pthread.inc_hpp.

(* Shared resources for the five downstream callable contracts:
   - Successful init(NULL) takes mutex_available and custody of P, and
     supplies mutex_ready. Its own contract accounts for failure results.
   - Lock preserves mutex_live and replaces its mutex_access loan with
     mutex_held for the executing thread and ownership of P on success.
   - Trylock has the same success transition. EBUSY preserves the caller's
     access loan, or preserves its existing held token for an owner call.
   - Unlock requires mutex_owned for the same thread and returns the loan
     after putting the protected resource back into mutex_live.
   - Destroy needs mutex_live and the full access loan, and returns
     mutex_available and P when its transition succeeds.

   A user waiting to acquire retains a positive access loan throughout the
   call. A held loan is reserved in the invariant and the held token until
   unlock. Choose process-local protected resources for cross-thread use. *)

Require Import skylabs.auto.cpp.proof.

Section static_initializer.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.

  (* Exact active-member view of the selected x86-64 GNU C++17 expansion.
     No value is specified for padding or an inactive union member. *)
  Definition mutex_static_initializerR : Rep :=
    unionR "pthread_mutex_t" 1$m (Some 0%nat) **
    (_field "pthread_mutex_t::__data" |->
      (structR "__pthread_mutex_s" 1$m **
       (_field "__pthread_mutex_s::__lock" |-> primR "int" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__count" |-> primR "unsigned int" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__owner" |-> primR "int" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__nusers" |-> primR "unsigned int" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__kind" |-> primR "int" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__spins" |-> primR "short" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__elision" |-> primR "short" 1$m (Vint 0)) **
       (_field "__pthread_mutex_s::__list" |->
         (structR "__pthread_internal_list" 1$m **
          (_field "__pthread_internal_list::__prev" |->
            primR (Tptr "__pthread_internal_list") 1$m (Vptr nullptr)) **
          (_field "__pthread_internal_list::__next" |->
            primR (Tptr "__pthread_internal_list") 1$m (Vptr nullptr)))))).

  (* A startup integration must supply this resource for the declared
     PTHREAD_MUTEX_INITIALIZER global before executing user code.
     The binding alone supplies symbol validity. The startup production
     and transfer into mutex_ready require a separate proof. *)
  Definition mutex_static_startup (name : obj_name) : mpred :=
    _global name |-> mutex_static_initializerR.
End static_initializer.
