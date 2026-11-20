(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.auto.cpp.local_with.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.brick.libstdcpp.runtime.objective.
Require Import iris.algebra.lib.excl_auth.
Require Export skylabs.brick.libstdcpp.pthread.mutex_unlock.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex.spec.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.

  (* This boundary models release by the executing owner of a live default
     normal, process-private, non-robust mutex. The held loan and protected
     resource are deposited into the protocol, restoring the access loan. *)
  cpp.spec "pthread_mutex_unlock"
    from source
    as pthread_mutex_unlock_spec
    with (\arg{p : ptr} "__mutex" (Vptr p)
          \prepost{(g : mutex_generation) (P : mpred)} mutex_live p g P
          \prepost{owner : thread_idT} current_thread owner
          \pre{q : Qp} mutex_held g owner q
          \pre P
          \require LocalWith procTI P
          \post[Vint 0] mutex_access g q).
End with_cpp.
