(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.join.join.spec.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Import skylabs.brick.libstdcpp.pthread.join.spec.
Require skylabs.brick.libstdcpp.test.pthread.join.join_cpp.
Require Import skylabs.brick.libstdcpp.runtime.objective.
Require Import skylabs.bi.tls_modalities.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.join.join_cpp.source.

#[local] Hint Opaque peer_pre peer_post message_fields message_target message_unset worker_right
  composition_result pthread_create.starter_specR pthread_create.registry_sync
  pthread_create.completion_right lifecycle.id_valid lifecycle.running lifecycle.joined
  lifecycle_join.slot_before lifecycle_join.slot_after : sl_opacity.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.
  Local Open Scope cQp_scope.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry,
    !pthread_join.ProcessWaitDiscipline}.
  Set Default Proof Using "MOD".
  #[local] Existing Instance pthread_create.create_spec_spec_instance.
  #[local] Existing Instance pthread_join.join_spec_spec_instance.

  Local Lemma peer_callback_rep :
    join_peer_start_spec ⊢ _global peer_start_name |->
      pthread_create.starter_specR peer_arguments peer_pre peer_post.
  Proof.
    rw /join_peer_start_spec /specifications.specify
      pthread_create.starter_specR.unlock /peer_start_name /pthread_create.starter_kind.
    reflexivity.
  Qed.

  #[local] Instance peer_callback_affine (p : ptr) :
    Affine (p |-> pthread_create.starter_specR peer_arguments peer_pre peer_post).
  Proof. rw pthread_create.starter_specR.unlock. apply _. Qed.

  Local Lemma peer_pre_local message w
      (Hsync : LocalWith procTI (pthread_create.registry_sync pthread_create.registry_name))
      (Hpost : forall result, LocalWith procTI (worker_post w result)) :
    LocalWith procTI (peer_pre message (peer_argument w)).
  Proof.
    rw /peer_pre /peer_argument /model_of_peer /message_fields /message_target /worker_right
      pthread.R.unlock.
    typeclasses eauto.
  Qed.

  Local Lemma peer_post_local message w peer returned
      (Hpost : forall result, LocalWith procTI (worker_post w result))
      (Hjoined : forall tid gen result, LocalWith procTI (lifecycle.joined tid gen result)) :
    LocalWith procTI (peer_post message (peer_argument w) peer returned).
  Proof.
    rw /peer_post /peer_argument /model_of_peer.
    destruct (bool_decide (peer = worker_tid w));
      rw /message_fields /message_target pthread.R.unlock;
      try rw /worker_right;
      typeclasses eauto.
  Qed.

  #[local] Hint Resolve peer_pre_local peer_post_local : pure.

  Local Lemma retain_pure (proposition : Prop) :
    (⌜proposition⌝ : mpred) ⊢ [| proposition |] ∗ True.
  Proof.
    iIntros "%Hp".
    iSplitL ""; first by iPureIntro.
    done.
  Qed.

  Lemma create_then_join_via_peer_ok :
    verify[source] "create_then_join_via_peer".
  Proof.
    verify_spec.
    rw /message_fields /message_unset.
    go.
    iExists argT, Pre, Post, args.
    go $usenamed=true.
    rename _x_5 into worker_status.
    destruct (decide (worker_status = 0%Z)) as [-> | Hworker_failure].
    2: {
      have Hnonzero : bool_decide (worker_status <> 0%Z) = true by apply bool_decide_true.
      have Hnotzero : bool_decide (worker_status = 0%Z) = false by apply bool_decide_false.
      rw Hnotzero Hnonzero.
      go.
      rw /composition_result /message_fields /message_unset /lifecycle_join.slot_before.
      iLeft.
      go.
    }
    iAssert (pthread_create.registry_sync pthread_create.registry_name) with "[$]" as "#Hregistry".
    go.
    pose (w := {| worker_tid := tid; worker_gen := g; store_result := store;
                  worker_post := Post state args tid |}).
    have Hwait : forall peer, peer <> tid -> ~ pthread_join.may_wait_path tid peer.
    { intros peer Hdistinct. apply H2. congruence. }
    have Hlocal : LocalWith procTI (peer_pre message (peer_argument w)).
    { apply peer_pre_local; [exact H5 | exact (H4 tid)]. }
    iExists peer_arguments, peer_pre, peer_post, (peer_argument w).
    iPoseProof (peer_callback_rep with "[$]") as "Hpeer_callback".
    rw /peer_pre /peer_argument /model_of_peer /w /message_fields /message_target /worker_right.
    go $usenamed=true.
    rename _x_5 into peer_status.
    destruct (decide (peer_status = 0%Z)) as [-> | Hpeer_failure].
    2: {
      have Hnonzero : bool_decide (peer_status <> 0%Z) = true by apply bool_decide_true.
      have Hnotzero : bool_decide (peer_status = 0%Z) = false by apply bool_decide_false.
      rw Hnotzero Hnonzero.
      go.
      iExists (None : option ptr), g, (Post state args tid), (None : option val).
      rw /lifecycle_join.slot_before.
      go.
      iRename select (⌜tid <> creator⌝)%I into "Hraw_distinct".
      iDestruct (retain_pure (tid <> creator) with "Hraw_distinct") as "(%Htid & Htid_frame)".
      iSplitL ""; first by iPureIntro; congruence.
      iSplitL ""; first by iPureIntro; exact (H2 tid creator Htid).
      go.
      rw /composition_result /message_fields /message_target /lifecycle_join.slot_before.
      iRight. iLeft.
      match goal with
      | result : ptr |- _ =>
          iExists tid, g, result; solve [go]
      end.
    }
    go.
    rename tid into peer.
    rename g into peer_gen.
    iExists (Some result_slot), peer_gen, (peer_post message (peer_argument w) peer), prior_result.
    rw /lifecycle_join.slot_before.
    go.
    iRename select (⌜peer <> creator⌝)%I into "Hraw_distinct".
    iDestruct (retain_pure (peer <> creator) with "Hraw_distinct") as "(%Hpeer & Hpeer_frame)".
    iSplitL ""; first by iPureIntro; congruence.
    iSplitL ""; first by iPureIntro; exact (H2 peer creator Hpeer).
    go.
    rename _x_6 into returned.
    iRename select (peer_post message (peer_argument w) peer returned) into "Hpeer_post".
    iEval (rw /peer_post /peer_argument /model_of_peer /w;
           cbn [worker_tid worker_gen store_result worker_post]) in "Hpeer_post".
    destruct (bool_decide (peer = _tid_)) eqn:Hsame.
    all: iEval (try rw Hsame) in "Hpeer_post".
    - iDestruct "Hpeer_post" as "[Htarget Hpayload]".
      iDestruct "Hpayload" as "(Hreturned & Hfields & Hright)".
      iEval (rw /message_fields) in "Hfields".
      iDestruct "Hfields" as "(Hlayout & Hstore & Hflag)".
      go.
      iExists (1$m). go $usenamed=true.
      rw /composition_result.
      iRight. iRight.
      iExists peer, _g_, peer, peer_gen, returned.
      have Hreflexive : bool_decide (peer = peer) = true by apply bool_decide_true.
      rw Hreflexive /peer_post /peer_argument /model_of_peer Hreflexive
        /message_fields /message_target.
      iClear "Hregistry".
      iRename select (pthread_create.registry_sync pthread_create.registry_name)
        into "Hsync_duplicate".
      iRename select (⌜peer <> creator⌝)%I into "Hraw_first".
      iSplitL "Hpeer_frame Hsync_duplicate Hraw_first"; first by iPureIntro.
      go $usenamed=true.
    - iDestruct "Hpeer_post" as "[Htarget Hpayload]".
      iDestruct "Hpayload" as (worker_result) "(Hreturned & Hfields & Hjoined & Hworker)".
      iEval (rw /message_fields) in "Hfields".
      iDestruct "Hfields" as "(Hlayout & Hstore & Hflag)".
      go.
      iExists (1$m). go $usenamed=true.
      rw /composition_result.
      iRight. iRight.
      iExists _tid_, _g_, peer, peer_gen, returned.
      have Hdistinct : bool_decide (peer = _tid_) = false.
      { first [exact Hsame | apply bool_decide_false; assumption]. }
      rw Hdistinct /peer_post /peer_argument /model_of_peer Hdistinct
        /message_fields /message_target.
      iClear "Hregistry".
      iRename select (pthread_create.registry_sync pthread_create.registry_name)
        into "Hsync_duplicate".
      iRename select (⌜_tid_ <> creator⌝)%I into "Hraw_first".
      iSplitL "Hpeer_frame Hsync_duplicate Hraw_first"; first by iPureIntro.
      go $usenamed=true; try (iExists worker_result; go $usenamed=true).
  Qed.
End with_cpp.
