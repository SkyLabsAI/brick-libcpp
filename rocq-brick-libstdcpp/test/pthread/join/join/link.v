(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Import skylabs.brick.libstdcpp.pthread.join.spec.
Require Import skylabs.brick.libstdcpp.pthread.self.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.join.join.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.join.join.proof.
Require skylabs.brick.libstdcpp.test.pthread.join.join_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.join.join_cpp.source.

Section client_link.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry,
    !pthread_join.ProcessWaitDiscipline}.
  Set Default Proof Using "MOD".

  Lemma join_creator_linked :
    denoteModule source ∗ pthread_join.join_spec ⊢ join_creator_spec.
  Proof.
    iIntros "[#Hmodule #Hjoin]".
    iApply join_creator_ok.
    - iExact "Hmodule".
    - iNext. iExact "Hjoin".
  Qed.

  Lemma join_peer_start_linked :
    denoteModule source ∗ pthread_join.join_spec ∗ pthread_self_spec ⊢
      join_peer_start_spec.
  Proof.
    iIntros "(#Hmodule & #Hjoin & #Hself)".
    iApply join_peer_start_ok.
    - iExact "Hmodule".
    - iSplitL ""; iNext; iAssumption.
  Qed.

  Lemma create_then_join_via_peer_linked :
    denoteModule source ∗ pthread_create.create_spec ∗
      pthread_join.join_spec ∗ pthread_self_spec ⊢
    create_then_join_via_peer_spec.
  Proof.
    iIntros "(#Hmodule & #Hcreate & #Hjoin & #Hself)".
    iPoseProof (join_peer_start_linked with "[$Hmodule $Hjoin $Hself]") as "#Hpeer".
    iApply create_then_join_via_peer_ok.
    - iExact "Hmodule".
    - repeat iSplitL ""; iNext; iAssumption.
  Qed.
End client_link.
