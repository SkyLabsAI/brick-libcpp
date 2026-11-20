(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.iris.extra.bi.own.
Require Export skylabs.brick.libstdcpp.pthread.mutex_destroy.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex.spec.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.
  Context `{!HasStdThreads Σ}.

  (* The full access share excludes holders and outstanding access loans
     in this live default mutex generation. Retired storage and P are
     the resources for a subsequent default initialization. *)
  cpp.spec "pthread_mutex_destroy"
    from source
    as pthread_mutex_destroy_spec
    with (\arg{p : ptr} "__mutex" (Vptr p)
          \prepost{tid : thread_idT} current_thread tid
          \pre{(g : mutex_generation) (P : mpred)}
            mutex_live p g P ** mutex_access g 1%Qp
          \post[Vint 0] mutex_available p ** P).
End with_cpp.
