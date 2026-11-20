(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.join.join.spec.
Require Import skylabs.brick.libstdcpp.pthread.self.spec.
Require Import skylabs.brick.libstdcpp.pthread.join.spec.
Require skylabs.brick.libstdcpp.test.pthread.join.join_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.join.join_cpp.source.

#[local] Hint Opaque peer_pre peer_post message_fields message_target worker_right worker_post
  pthread_create.registry_sync pthread_create.completion_right lifecycle.id_valid
  lifecycle.running lifecycle.joined lifecycle_join.slot_before lifecycle_join.slot_after : sl_opacity.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry,
    !pthread_join.ProcessWaitDiscipline}.
  Set Default Proof Using "MOD".
  #[local] Existing Instance pthread_join.join_spec_spec_instance.

  Local Lemma thread_id_value_inj (a b : thread_idT) :
    wrap.unwrapN a = wrap.unwrapN b -> a = b.
  Proof. by destruct a, b; simpl; intros ->. Qed.

  Lemma join_peer_start_ok :
    verify[source] "join_peer_start".
  Proof.
    verify_spec.
    rw /peer_pre /message_fields /message_target /worker_right.
    go.
    destruct (bool_decide (wrap.unwrapN tid =
      wrap.unwrapN (worker_tid (model_of_peer arg)))) eqn:Hguard.
    2: {
      have Hdifferent : tid <> worker_tid (model_of_peer arg).
      { intros Heq. apply bool_decide_eq_false in Hguard. apply Hguard. by rw Heq. }
      have Hpost : bool_decide (tid = worker_tid (model_of_peer arg)) = false
        by apply bool_decide_false.
      go.
      have Hsafe : ~ pthread_join.may_wait_path (worker_tid (model_of_peer arg)) tid by eauto.
      destruct (store_result (model_of_peer arg)) eqn:Hstore.
      + go.
        iExists (Some result_addr), (worker_gen (model_of_peer arg)),
          (worker_post (model_of_peer arg)), (Some (Vptr argp)).
        rw /lifecycle_join.slot_arg /lifecycle_join.slot_before.
        go.
        iDestruct (type_ptr_nonnull "void*" result_addr with "[$]") as %Hnonnull.
        iSplitL ""; first by iPureIntro.
        iIntros (result) "(Hthread & Hregistry & Hjoined & Hworker & Hslot)".
        iDestruct (lifecycle_join.writable_after result_addr result with "Hslot") as "Hslot".
        go $usenamed=true.
        rw /peer_post ?Hpost ?Hstore /message_target /message_fields.
        go $usenamed=true.
        iExists result.
        go $usenamed=true.
      + go.
        iExists (None : option ptr), (worker_gen (model_of_peer arg)),
          (worker_post (model_of_peer arg)), (None : option val).
        rw /lifecycle_join.slot_arg lifecycle_join.discard_before.
        go.
        lazymatch goal with
        | |- context [lifecycle.joined (worker_tid _) (worker_gen _) ?value] =>
          rename value into result
        end.
        rw ?lifecycle_join.discard_after.
        go.
        rw /peer_post ?Hpost ?Hstore /message_target /message_fields.
        go.
        iExists result.
        go.
    }
    - have Hsame : tid = worker_tid (model_of_peer arg).
      { apply thread_id_value_inj. apply bool_decide_eq_true in Hguard. exact Hguard. }
      have Hpost : bool_decide (tid = worker_tid (model_of_peer arg)) = true
        by apply bool_decide_true.
      go.
      rw /peer_post ?Hpost /message_target /message_fields /worker_right.
      go.
  Qed.
End with_cpp.
