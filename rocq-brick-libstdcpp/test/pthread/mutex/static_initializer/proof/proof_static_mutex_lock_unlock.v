(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.
  Set Default Proof Using "MOD".

  Local Definition mutex_ready_open_F := [FWD->] mutex_ready_open.

  Lemma static_mutex_lock_unlock_ok :
    verify[source] static_mutex_lock_unlock_spec.
  Proof.
    verify_spec; go using mutex_ready_open_F.
    iExists g, P, 1%Qp.
    go.
    unfold mutex_lock_result.
    iDestruct select (_ ∨ _)%I as "[(-> & Hheld & HP) | (%Hd & Hacc)]"; last by destruct Hd.
    go.
    iExists g, P, 1%Qp.
    go.
    iFrame "Hheld HP".
    go.
    iExists g. go.
  Qed.
End with_cpp.
