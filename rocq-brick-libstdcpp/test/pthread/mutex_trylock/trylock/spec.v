(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.iris.extra.bi.own.
Require Import skylabs.bi.tls_modalities.
Require Export skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex_trylock.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.
  Context `{!HasStdThreads Σ}.

  cpp.spec "trylock_uncontended(pthread_mutex_t*)" as trylock_uncontended_spec with
    (\arg{p : ptr} "mutex" (Vptr p)
     \prepost{(g : mutex_generation) (P : mpred)} mutex_live p g P
     \require (LocalWith procTI P)
     \prepost{owner : thread_idT} current_thread owner
     \pre mutex_access g 1%Qp
     \post[Vbool true] (mutex_held g owner 1%Qp ** P)).

  cpp.spec "trylock_current_owner(pthread_mutex_t*)" as trylock_current_owner_spec with
    (\arg{p : ptr} "mutex" (Vptr p)
     \prepost{(g : mutex_generation) (P : mpred)} mutex_live p g P
     \require (LocalWith procTI P)
     \prepost{owner : thread_idT} current_thread owner
     \prepost{q : Qp} mutex_held g owner q
     \prepost P
     \post[Vbool true] emp).

  Context `{state_valid : !HasOwnValid (iPropI _Σ) (excl_authR mutex_stateO)}.

  (* The frame models the peer continuing to hold the same generation
     throughout the observation. It never supplies this caller's identity
     and the caller receives neither peer storage nor a held right. *)
  cpp.spec "trylock_peer_contention(pthread_mutex_t*)" as trylock_peer_contention_spec with
    (\arg{p : ptr} "mutex" (Vptr p)
     \prepost{(g : mutex_generation) (P : mpred)} mutex_live p g P
     \require (LocalWith procTI P)
     \prepost{owner : thread_idT} current_thread owner
     \prepost{q : Qp} mutex_access g q
     \prepost{(peer : thread_idT) (peer_q : Qp)} mutex_held g peer peer_q
     \require (peer <> owner)
     \post[Vbool true] emp).
End with_cpp.
