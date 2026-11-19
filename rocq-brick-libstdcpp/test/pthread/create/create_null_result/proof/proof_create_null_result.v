(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.create.create_null_result.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.create.create_null_result.proof.proof_create_null_start.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Import skylabs.brick.libstdcpp.runtime.objective.
Require Import skylabs.bi.tls_modalities.
Require skylabs.brick.libstdcpp.test.pthread.create.create_null_result_cpp.

Import auto.telescopes.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.create.create_null_result_cpp.source.

#[local] Hint Opaque pthread_create.registry_sync pthread_create.starter_specR
  pthread_create.completion_right lifecycle.id_valid : sl_opacity.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.
  Set Default Proof Using "MOD".

  #[local] Existing Instance pthread_create.create_spec_spec_instance.

  #[local] Instance null_start_rep_affine (p : ptr) :
    Affine (p |-> pthread_create.starter_specR tO null_pre null_post).
  Proof. rw pthread_create.starter_specR.unlock. apply _. Qed.

  Local Lemma null_start_callable :
    denoteModule source |--
      _global "create_null_start" |-> pthread_create.starter_specR tO null_pre null_post.
  Proof.
    rw pthread_create.starter_specR.unlock.
    exact create_null_start_ok.
  Qed.

  Local Lemma null_pre_local argp arg : LocalWith procTI (null_pre argp arg).
  Proof. rw /null_pre. apply _. Qed.

  Local Lemma null_post_local argp arg tid result : LocalWith procTI (null_post argp arg tid result).
  Proof. rw /null_post. apply _. Qed.

  #[local] Hint Resolve null_pre_local null_post_local : pure.

  Lemma create_null_result_ok :
    verify[source] "create_null_result".
  Proof.
    verify_spec.
    go.
    iExists tO, null_pre, null_post, null_arguments.
    iSplitL "".
    { wapply null_start_callable. go. }
    go.
    rename _x_ into status.
    destruct (decide (status = 0%Z)) as [-> | Hstatus].
    - go.
      iExists tid, g.
      go.
    - have Hfailure : bool_decide (status = 0%Z) = false by apply bool_decide_false.
      have Hbranch : bool_decide (status <> 0%Z) = true by apply bool_decide_true.
      rw Hfailure Hbranch /null_pre.
      go.
  Qed.
End with_cpp.
