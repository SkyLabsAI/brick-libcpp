(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.create.pred.
Require skylabs.brick.libstdcpp.pthread.inc_hpp.
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.bi.tls_modalities.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Module pthread_create.
  Export pthread_create.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Definition starter_kind : okind :=
    tFunction (cc:=CC_C) "void*" ["void*"%cpp_type].

  Definition starter_spec `{Σ : cpp_logic, σ : genv}
      `{!HasStdThreads Σ, !lifecycle.G _Σ}
      (argT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> thread_idT -> ptr -> mpred) : WpSpec_cpp_val :=
    \arg{argp} "arg" (Vptr argp)
    \prepost{tid} current_thread tid
    \pre{arg g} Pre argp arg ∗ lifecycle.running tid g
    \post{result}[Vptr result] lifecycle.running tid g ∗ Post argp arg tid result.

  mlock
  Definition starter_specR `{Σ : cpp_logic, σ : genv}
      `{!HasStdThreads Σ, !lifecycle.G _Σ}
      (argT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> thread_idT -> ptr -> mpred) : Rep :=
    unmaterialized_specR starter_kind (starter_spec argT Pre Post).

  Section external.
    Context `{Σ : cpp_logic, σ : genv}.
    Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !ProcessRegistry}.

    (** Callable premise for the pinned public declaration. The process uses
        ordinary joinable defaults. GNU default-attribute changes, detachment,
        cancellation, pthread_exit and non-normal callback return are outside
        this contract. Successful commit establishes a registered generation
        and its escrow before the callback starts. The creator may return
        before or after the worker starts or finishes. A nonzero status leaves
        the argument with the creator and starts no worker. Its output slot
        is still writable with unspecified contents. The status gives no
        progress, timing, fairness, or exact errno guarantee. *)
    #[local] cpp.spec "pthread_create"
      from source
      as create_spec
      with ( \arg{idp} "tid" (Vptr idp)
             \pre idp |-> anyR "unsigned long" 1$m
             \arg "attr" (Vptr nullptr)
             \arg{starterp} "start" (Vptr starterp)
             \with argT Pre Post
             \prepost starterp |-> starter_specR argT Pre Post
             \arg{argp} "arg" (Vptr argp)
             \pre{arg : argT} Pre argp arg
             \prepost{creator} current_thread creator
             \prepost registry_sync registry_name
             \require LocalWith procTI (Pre argp arg)
             \require forall tid result, LocalWith procTI (Post argp arg tid result)
             \post{err}[Vint err]
                 if bool_decide (err = 0) then
                   ∃ tid g,
                     ⌜tid <> creator⌝ ∗ idp |-> pthread.R 1$m tid ∗
                     lifecycle.id_valid registry_name 1 tid g ∗
                     completion_right registry_name tid g (Post argp arg tid)
                 else
                   Pre argp arg ∗ idp |-> anyR "unsigned long" 1$m ).
  End external.
End pthread_create.
