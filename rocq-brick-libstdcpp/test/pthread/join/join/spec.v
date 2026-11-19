(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Import skylabs.brick.libstdcpp.pthread.join.spec.
Require Export skylabs.brick.libstdcpp.test.pthread.join.join.pred.
Require skylabs.brick.libstdcpp.test.pthread.join.join_cpp.
Require Import skylabs.bi.tls_modalities.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.join.join_cpp.source.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.

  Context `{!pthread_join.ProcessWaitDiscipline}.

  cpp.spec "join_creator"
    from source
    as join_creator_spec
    with ( \arg{tid : thread_idT} "target" (Vthread tid)
           \arg{slot : option ptr} "slot" (Vptr (lifecycle_join.slot_arg slot))
           \prepost{joiner : thread_idT} current_thread joiner
           \require (joiner <> tid)
           \require (~ pthread_join.may_wait_path tid joiner)
           \prepost pthread_create.registry_sync pthread_create.registry_name
           \pre{g : lifecycle.generation}
             lifecycle.id_valid pthread_create.registry_name 1 tid g
           \pre{Post : ptr -> mpred}
             pthread_create.completion_right pthread_create.registry_name tid g Post
           \pre{old : option val} lifecycle_join.slot_before slot old
           \post{result : ptr}[Vint 0]
             lifecycle.joined tid g result ∗ Post result ∗
               lifecycle_join.slot_after slot result ).

  Record peer_model := {
    worker_tid : thread_idT;
    worker_gen : lifecycle.generation;
    store_result : bool;
    worker_post : ptr -> mpred;
  }.

  Definition peer_arguments : tele := tS (fun _ : peer_model => tO).

  Definition peer_argument (w : peer_model) : tele_arg peer_arguments.
  Proof. constructor; [exact w | constructor]. Defined.

  Definition model_of_peer (args : tele_arg peer_arguments) : peer_model.
  Proof. destruct args as [model _]. exact model. Defined.

  Definition message_fields (m : ptr) (store : bool) (flag : option val) : mpred :=
    (m |-> structR "join_message" 1$m ∗
     m |-> (_field "join_message::store_result" |-> primR "bool" 1$m (Vbool store)) ∗
     m |-> (_field "join_message::joined_target" |-> oprimR "bool" 1$m flag))%I.

  Definition message_target (m : ptr) (tid : thread_idT) : mpred :=
    (m |-> (_field "join_message::target" |-> pthread.R 1$m tid))%I.

  Definition message_unset (m : ptr) : mpred :=
    (m |-> (_field "join_message::target" |-> anyR "unsigned long" 1$m))%I.

  Definition worker_right (w : peer_model) : mpred :=
    (lifecycle.id_valid pthread_create.registry_name 1 w.(worker_tid) w.(worker_gen) ∗
     pthread_create.completion_right pthread_create.registry_name
       w.(worker_tid) w.(worker_gen) w.(worker_post))%I.

  Definition peer_pre (m : ptr) (args : tele_arg peer_arguments) : mpred :=
    let w := model_of_peer args in
    (pthread_create.registry_sync pthread_create.registry_name ∗
     message_fields m w.(store_result) None ∗ message_target m w.(worker_tid) ∗
     worker_right w ∗ [| forall peer, peer <> w.(worker_tid) ->
       ~ pthread_join.may_wait_path w.(worker_tid) peer |])%I.

  Definition peer_post (m : ptr) (args : tele_arg peer_arguments)
      (peer : thread_idT) (returned : ptr) : mpred :=
    let w := model_of_peer args in
    (message_target m w.(worker_tid) ∗
     if bool_decide (peer = w.(worker_tid)) then
       ⌜returned = nullptr⌝ ∗ message_fields m w.(store_result) (Some (Vbool false)) ∗
       worker_right w
     else
       ∃ result, ⌜returned = if w.(store_result) then result else nullptr⌝ ∗
         message_fields m w.(store_result) (Some (Vbool true)) ∗
         lifecycle.joined w.(worker_tid) w.(worker_gen) result ∗ w.(worker_post) result)%I.

  Definition peer_start_name : globname := Nglobal (Nid "join_peer_start").

  cpp.spec "join_peer_start"
    from source
    as join_peer_start_spec
    with (pthread_create.starter_spec peer_arguments peer_pre peer_post).

  Definition composition_result (message peer_slot result_slot : ptr)
      (store : bool) (prior_result : option val)
      (Entry : mpred) (Exit : thread_idT -> ptr -> mpred) (status : Z) : mpred :=
    ((⌜status <> 0%Z⌝ ∗
      message_fields message store None ∗ message_unset message ∗
      peer_slot |-> anyR "unsigned long" 1$m ∗
      lifecycle_join.slot_before (Some result_slot) prior_result ∗ Entry)
     ∨ (∃ target gen result, ⌜status <> 0%Z⌝ ∗
        message_fields message store None ∗ message_target message target ∗
        peer_slot |-> anyR "unsigned long" 1$m ∗
        lifecycle_join.slot_before (Some result_slot) prior_result ∗
        lifecycle.joined target gen result ∗ Exit target result)
     ∨ (∃ target gen peer peer_gen returned,
        ⌜status = (if bool_decide (peer = target) then -1 else 0)%Z⌝ ∗
        peer_slot |-> pthread.R 1$m peer ∗
        lifecycle_join.slot_after (Some result_slot) returned ∗
        lifecycle.joined peer peer_gen returned ∗
        peer_post message (peer_argument {| worker_tid := target; worker_gen := gen;
                   store_result := store; worker_post := Exit target |}) peer returned))%I.

  cpp.spec "create_then_join_via_peer"
    from source
    as create_then_join_via_peer_spec
    with ( \arg{message} "message" (Vptr message)
           \pre{store} message_fields message store None ∗ message_unset message
           \arg{peer_slot} "peer" (Vptr peer_slot)
           \pre peer_slot |-> anyR "unsigned long" 1$m
           \arg{result_slot} "peer_result" (Vptr result_slot)
           \pre{prior_result} lifecycle_join.slot_before (Some result_slot) prior_result
           \arg{callback} "worker_start" (Vptr callback)
           \with argT Pre Post
           \prepost callback |-> pthread_create.starter_specR argT Pre Post
           \arg{state} "worker_argument" (Vptr state)
           \pre{args : argT} Pre state args
           \prepost{creator} current_thread creator
           \prepost pthread_create.registry_sync pthread_create.registry_name
           \require forall a b, a <> b -> ~ pthread_join.may_wait_path a b
           \require LocalWith procTI (Pre state args)
           \require forall tid result, LocalWith procTI (Post state args tid result)
           \require LocalWith procTI (pthread_create.registry_sync pthread_create.registry_name)
           \require forall tid gen result, LocalWith procTI (lifecycle.joined tid gen result)
           \post{status}[Vint status]
             composition_result message peer_slot result_slot store prior_result
               (Pre state args) (Post state args) status ).
End with_cpp.
