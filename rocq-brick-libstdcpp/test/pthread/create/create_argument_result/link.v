(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.create.create_argument_result.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.create.create_argument_result.proof.proof_create_argument_start.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require skylabs.brick.libstdcpp.test.pthread.create.create_argument_result_cpp.
Require Import skylabs.brick.libstdcpp.test.pthread.create.create_argument_result.proof.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.create.create_argument_result_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.
  Set Default Proof Using "MOD".

  Lemma create_argument_result_linked :
    denoteModule source ∗ pthread_create.create_spec ⊢ create_argument_result_spec.
  Proof.
    iIntros "[#Hsource #Hcreate]".
    iPoseProof (create_argument_start_ok with "Hsource") as "#Hstart".
    iApply create_argument_result_ok.
    - iExact "Hsource".
    - iSplitL "".
      + iNext. iExact "Hstart".
      + iNext. iExact "Hcreate".
  Qed.
End with_cpp.
