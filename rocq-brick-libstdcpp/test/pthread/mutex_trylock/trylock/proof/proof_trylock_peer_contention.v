(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.iris.extra.bi.own.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock_cpp.

Import linearity.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock_cpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} `{MOD : source ⊧ σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.
  Context `{!HasStdThreads Σ}.
  Context `{state_valid : !HasOwnValid (iPropI _Σ) (excl_authR mutex_stateO)}.
  Set Default Proof Using "MOD".

  Lemma trylock_peer_contention_ok :
    verify[source] "trylock_peer_contention(pthread_mutex_t*)".
  Proof using MOD state_valid.
    verify_spec; go.
    iExists g, P, q, false.
    work.
    iDestruct select (mutex_access g q) as "Hloan".
    iSplitL "Hloan".
    { iLeft. by iFrame "Hloan". }
    iIntros (ret) "(? & ? & Hresult)".
    iDestruct "Hresult" as "[(%Hr & Hnew & ?) | [(%Hr & ?) | (%Hr & ?)]]".
    - (* The stable peer frame rules out a second held token. *)
      iDestruct select (mutex_held g peer peer_q) as "Hpeer".
      iDestruct (mutex_held_exclusive g owner peer q peer_q with "[Hnew Hpeer]") as %[].
      iFrame.
    - destruct Hr as [_ [_ ->]]. go.
    - destruct Hr as [Hmode _]. discriminate.

  Qed.
End with_cpp.
