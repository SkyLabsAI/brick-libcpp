(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.auto.cpp.local_with.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.brick.libstdcpp.runtime.objective.
Require Import iris.algebra.lib.excl_auth.
Require Export skylabs.brick.libstdcpp.test.pthread.mutex_unlock.unlock.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex_unlock.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex_unlock.unlock_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_unlock.unlock_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.

  cpp.spec "unlock_owned_mutex(pthread_mutex_t*)"
    from source
    as unlock_owned_mutex_spec
    with (\arg{p : ptr} "mutex" (Vptr p)
          \prepost{(g : mutex_generation) (P : mpred)} mutex_live p g P
          \pre{(owner : thread_idT) (q : Qp)} mutex_owned g owner q
          \pre P
          \require LocalWith procTI P
          \post[Vint 0] current_thread owner ** mutex_access g q).
End with_cpp.
