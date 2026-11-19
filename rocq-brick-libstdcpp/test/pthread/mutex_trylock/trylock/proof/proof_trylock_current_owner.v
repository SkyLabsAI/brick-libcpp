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
  Set Default Proof Using "MOD".

  Lemma trylock_current_owner_ok :
    verify[source] "trylock_current_owner(pthread_mutex_t*)".
  Proof.
    verify_spec; go.
    iExists g, P, q, true.
    work.
    iDestruct select (mutex_held g owner q) as "Hheld".
    iSplitL "Hheld".
    { iRight. by iFrame "Hheld". }
    iIntros (ret) "(? & ? & Hresult)".
    iDestruct "Hresult" as "[(%Hr & ? & ?) | [(%Hr & ?) | (%Hr & ?)]]".
    - destruct Hr as [Hmode _]. discriminate.
    - destruct Hr as [Hmode _]. discriminate.
    - destruct Hr as [_ ->]. go.

  Qed.
End with_cpp.
