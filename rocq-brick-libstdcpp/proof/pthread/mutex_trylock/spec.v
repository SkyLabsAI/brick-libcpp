(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.iris.extra.bi.own.
Require Import skylabs.bi.tls_modalities.
Require Export skylabs.brick.libstdcpp.pthread.mutex_trylock.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex.spec.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.
  Context `{!HasStdThreads Σ}.

  (* POSIX.1-2017 pthread_mutex_trylock DESCRIPTION and ERRORS, restricted
     to live default normal, process-private, non-robust mutexes. The access
     loan keeps the lifetime live under interference. A full loan excludes
     a holder and every other loan. An owner can retry with its held token,
     framing any protected resource already in its possession. *)
  cpp.spec "pthread_mutex_trylock" from source as pthread_mutex_trylock_spec with
    (\arg{p : ptr} "__mutex" (Vptr p)
     \prepost{(g : mutex_generation) (P : mpred)} mutex_live p g P
     \require (LocalWith procTI P)
     \prepost{owner : thread_idT} current_thread owner
     \pre{(q : Qp) (owns : bool)}
       (([| owns = false |] ** mutex_access g q) ∨
        ([| owns = true |] ** mutex_held g owner q))
     \post{ret : Z}[Vint ret]
       (([| owns = false /\ ret = 0%Z |] ** mutex_held g owner q ** P) ∨
        ([| owns = false /\ q <> 1%Qp /\ ret = pthread_mutex_trylock_ebusy |] **
          mutex_access g q) ∨
        ([| owns = true /\ ret = pthread_mutex_trylock_ebusy |] ** mutex_held g owner q))).
End with_cpp.
