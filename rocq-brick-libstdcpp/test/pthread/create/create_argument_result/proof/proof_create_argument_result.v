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

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.create.create_argument_result_cpp.source.

#[local] Hint Opaque argument_pre argument_post
  pthread_create.starter_specR pthread_create.registry_sync
  pthread_create.completion_right lifecycle.id_valid : sl_opacity.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.
  Set Default Proof Using "MOD".
  #[local] Existing Instance pthread_create.create_spec_spec_instance.

  #[local] Instance argument_callback_affine (p : ptr) :
    Affine (p |-> pthread_create.starter_specR tO argument_pre argument_post).
  Proof. rw pthread_create.starter_specR.unlock. apply _. Qed.

  Local Lemma argument_callback_rep :
    denoteModule source ⊢ _global argument_start_name |->
      pthread_create.starter_specR tO argument_pre argument_post.
  Proof.
    rw pthread_create.starter_specR.unlock.
    exact create_argument_start_ok.
  Qed.

  #[local] Hint Resolve argument_pre_local argument_post_local : pure.

  Lemma create_argument_result_ok :
    verify[source] "create_argument_result".
  Proof.
    verify_spec.
    go.
    iExists tO, argument_pre, argument_post, argument_model.
    iPoseProof (argument_callback_rep with "[$]") as "Hcallback".
    go $usenamed=true.
    rename _x_ into status.
    destruct (decide (status = 0%Z)) as [-> | Hstatus].
    - go.
      iExists tid, g.
      go.
    - have Hfailure : bool_decide (status = 0%Z) = false by apply bool_decide_false.
      have Hbranch : bool_decide (status <> 0%Z) = true by apply bool_decide_true.
      rw Hfailure Hbranch.
      go.
  Qed.
End with_cpp.
