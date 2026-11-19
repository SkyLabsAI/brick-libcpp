(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.iris.extra.bi.own.
Require Export skylabs.brick.libstdcpp.pthread.mutex_destroy.spec.
Require Export skylabs.brick.libstdcpp.test.pthread.mutex_destroy.destroy.pred.
Require skylabs.brick.libstdcpp.test.pthread.mutex_destroy.destroy_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_destroy.destroy_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.
  Context `{!HasStdThreads Σ}.

  cpp.spec "destroy_default_mutex(pthread_mutex_t*)"
    as destroy_default_mutex_spec
    with (\arg{p : ptr} "mutex" (Vptr p)
          \prepost{tid : thread_idT} current_thread tid
          \pre{(g : mutex_generation) (P : mpred)}
            mutex_live p g P ** mutex_access g 1%Qp
          \post[Vint 0] mutex_available p ** P).
End with_cpp.
