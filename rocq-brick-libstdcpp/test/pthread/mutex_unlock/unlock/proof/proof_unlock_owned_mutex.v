(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_unlock.unlock.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex_unlock.unlock_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_unlock.unlock_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.
  Set Default Proof Using "MOD".

  Local Definition open_mutex_owned := [FWD->] mutex_owned_open.

  Lemma unlock_owned_mutex_ok :
    verify[source] unlock_owned_mutex_spec.
  Proof.
    verify_spec; go using open_mutex_owned.
    iExists g, P, q.
    go.
  Qed.
End with_cpp.
