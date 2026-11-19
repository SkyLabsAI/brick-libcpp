(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.iris.extra.bi.own.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_init.init.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex_init.init_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_init.init_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{threads : !HasStdThreads Σ}.
  Context `{mutex_state_own : !HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.
  Set Default Proof Using "MOD".

  Local Lemma mutex_available_from_storage (p : ptr) :
    (mutex_available p ∨ (p |-> uninitR "pthread_mutex_t" 1$m))%I |-- mutex_available p.
  Proof.
    iIntros "[Havailable | Huninitialized]".
    - iExact "Havailable".
    - iApply (mutex_available_from_uninitialized with "Huninitialized").
  Qed.

  Local Definition mutex_available_from_storage_F := [FWD] mutex_available_from_storage.
  Local Definition mutex_ready_open_F := [FWD->] mutex_ready_open.

  Lemma init_default_mutex_ok :
    verify[source] init_default_mutex_spec.
  Proof.
    verify_spec.
    go using mutex_available_from_storage_F.
    iExists P.
    go using mutex_available_from_storage_F, mutex_ready_open_F.
    case_bool_decide; go using mutex_ready_open_F.
    iExists g. go.
  Qed.
End with_cpp.
