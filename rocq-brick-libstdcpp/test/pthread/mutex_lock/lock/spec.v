(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Export skylabs.brick.libstdcpp.test.pthread.mutex_lock.lock.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex_lock.spec.
Require Import skylabs.bi.tls_modalities.
Require Import iris.algebra.lib.excl_auth.
Require skylabs.brick.libstdcpp.test.pthread.mutex_lock.lock_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_lock.lock_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ, source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.

  cpp.spec "lock_live(pthread_mutex_t*)"
    as lock_live_spec
    with (\arg{p : ptr} "mutex" (Vptr p)
          \prepost{(g : mutex_generation) (P : mpred) (owner : thread_idT)}
            mutex_live p g P ** current_thread owner
          \require (LocalWith procTI P)
          \pre{q : Qp} mutex_access g q
          \post{ret : Z}[Vint ret] mutex_lock_result g owner q P ret).
End with_cpp.
