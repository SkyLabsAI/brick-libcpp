(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_lock.lock.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex_lock.lock_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_lock.lock_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.
  Set Default Proof Using "MOD".

  Lemma lock_live_ok :
    verify[source] "lock_live(pthread_mutex_t*)".
  Proof.
    verify_spec; go.
    iExists g, P, q.
    go.
  Qed.
End with_cpp.
