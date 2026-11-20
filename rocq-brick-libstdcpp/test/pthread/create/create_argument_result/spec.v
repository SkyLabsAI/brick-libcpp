(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Export skylabs.brick.libstdcpp.test.pthread.create.create_argument_result.pred.
Require skylabs.brick.libstdcpp.test.pthread.create.create_argument_result_cpp.
Require Import skylabs.bi.tls_modalities.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.create.create_argument_result_cpp.source.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.

  Definition argument_model : tele_arg tO := ltac:(constructor).

  Definition argument_pre (state : ptr) (_ : tele_arg tO) : mpred :=
    (state |-> primR "int" 1$m (Vint 0))%I.

  Definition argument_post (state : ptr) (_ : tele_arg tO)
      (_ : thread_idT) (result : ptr) : mpred :=
    (⌜result = state⌝ ∗ state |-> primR "int" 1$m (Vint 3))%I.

  #[global] Instance argument_pre_local state arg :
    LocalWith procTI (argument_pre state arg).
  Proof. rw /argument_pre. apply _. Qed.

  #[global] Instance argument_post_local state arg tid result :
    LocalWith procTI (argument_post state arg tid result).
  Proof. rw /argument_post. apply _. Qed.

  Definition argument_start_name : globname := Nglobal (Nid "create_argument_start").

  cpp.spec "create_argument_start"
    from source
    as create_argument_start_spec
    with (pthread_create.starter_spec tO argument_pre argument_post).

  cpp.spec "create_argument_result"
    from source
    as create_argument_result_spec
    with ( \arg{idp} "created" (Vptr idp)
           \pre idp |-> anyR "unsigned long" 1$m
           \arg{state} "state" (Vptr state)
           \pre argument_pre state argument_model
           \prepost{creator} current_thread creator
           \prepost pthread_create.registry_sync pthread_create.registry_name
           \post{status}[Vint status]
             if bool_decide (status = 0) then
               ∃ tid g,
                 ⌜tid <> creator⌝ ∗ idp |-> pthread.R 1$m tid ∗
                 lifecycle.id_valid pthread_create.registry_name 1 tid g ∗
                 pthread_create.completion_right pthread_create.registry_name tid g
                   (argument_post state argument_model tid)
             else
               argument_pre state argument_model ∗ idp |-> anyR "unsigned long" 1$m ).
End with_cpp.
