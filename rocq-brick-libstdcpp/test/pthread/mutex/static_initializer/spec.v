(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Export skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex_lock.spec.
Require Export skylabs.brick.libstdcpp.pthread.mutex_unlock.spec.
Require Import skylabs.bi.tls_modalities.
Require Import iris.algebra.lib.excl_auth.
Require skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  cpp.spec "static_mutex_address"
    as static_mutex_address_spec default.

  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.

  (* BRiCk does not model program startup yet
     (https://github.com/SkyLabsAI/brick-libcpp/issues/263), so nothing proves
     that PTHREAD_MUTEX_INITIALIZER leaves [static_mutex] ready before [main].
     The precondition states it instead: the caller owns the global's ready
     mutex, the same resource a successful [pthread_mutex_init] produces. *)
  cpp.spec "static_mutex_lock_unlock"
    as static_mutex_lock_unlock_spec
    with (\prepost{owner : thread_idT} current_thread owner
          \with (P : mpred)
          \require LocalWith procTI P
          \pre mutex_ready (_global "static_mutex") P
          \post[Vint 0] ∃ g, mutex_live (_global "static_mutex") g P ** mutex_access g 1%Qp).
End with_cpp.
