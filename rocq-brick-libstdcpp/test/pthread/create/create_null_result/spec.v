(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Export skylabs.brick.libstdcpp.test.pthread.create.create_null_result.pred.
Require skylabs.brick.libstdcpp.test.pthread.create.create_null_result_cpp.

Import auto.telescopes auto.telescopes.TeleNotations.

Definition null_arguments : tele_arg tO := ltac:(constructor).

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.create.create_null_result_cpp.source.

Section payload.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition null_pre (argp : ptr) (_ : tO) : mpred :=
    (argp |-> primR "int" 1$m (Vint 0))%I.

  Definition null_post (argp : ptr) (_ : tO) (_ : thread_idT) (result : ptr) : mpred :=
    ([| result = nullptr |] ** argp |-> primR "int" 1$m (Vint 2))%I.
End payload.

#[global] Hint Opaque null_pre null_post : sl_opacity.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.

  cpp.spec "create_null_start"
    from source
    as create_null_start_spec
    with ( \arg{argp} "argument" (Vptr argp)
           \prepost{tid} current_thread tid
           \pre{(arg : tO) g} null_pre argp arg ∗ lifecycle.running tid g
           \post{result}[Vptr result] lifecycle.running tid g ∗ null_post argp arg tid result ).

  cpp.spec "create_null_result"
    from source
    as create_null_result_spec
    with ( \arg{idp} "created" (Vptr idp)
           \arg{argp} "state" (Vptr argp)
           \pre idp |-> anyR "unsigned long" 1$m
           \pre null_pre argp null_arguments
           \prepost{creator} current_thread creator
           \prepost pthread_create.registry_sync pthread_create.registry_name
           \post{err}[Vint err]
             if bool_decide (err = 0) then
               ∃ tid g,
                 ⌜tid <> creator⌝ ∗ idp |-> pthread.R 1$m tid ∗
                 lifecycle.id_valid pthread_create.registry_name 1 tid g ∗
                 pthread_create.completion_right pthread_create.registry_name tid g
                   (null_post argp null_arguments tid)
             else idp |-> anyR "unsigned long" 1$m ∗ argp |-> primR "int" 1$m (Vint 1) ).
End with_cpp.
