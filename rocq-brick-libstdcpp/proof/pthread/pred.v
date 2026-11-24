(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Export skylabs.brick.libstdcpp.runtime.objective.

Require Import skylabs.auto.cpp.prelude.spec.
(* TODO: add this to a prelude *)
Require Import skylabs.cpp.slice.

Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.

Import wrap.

Module pthread.

  Record gname := { _ghost : iprop.gname }.

  (** [handle γ tid P] is a token returned when thread creation succeeds. [P] is the
      postcondition of the thread. [handle] can be given to <<pthread_join>> to retrieve the
      ownership left by the thread's termination.

      [handle] does not record which thread may join: thread ids are reused once a thread is
      joined, so no thread-id check can rule out join cycles. <<pthread_join>> instead allows the
      <<EDEADLK>> error, which consumes the handle (SkyLabsAI/brick-libcpp#262). *)
  Parameter handle : forall `{Σ : cpp_logic,!HasStdThreads Σ}
                       (γ : gname) (tid : thread_idT)
                       (Post : mpred), mpred.

  mlock
  Definition R `{Σ : cpp_logic, σ : genv} (q : cQp.t) (id : thread_idT) :=
    ulongR q (unwrapN id).
  #[only(cfractional,cfracvalid,ascfractional,type_ptr,lazy_unfold)] derive R.

  (* TODO: fix [lazy_unfold] derivation. [q] and [q'] need to be distinct variables. *)
  #[global] Instance R_defined_using' `{Σ : cpp_logic, σ : genv} (q q' : cQp.t) (id : thread_idT) (arg : val) :
    lazy_unfold.AutoUnlocking.DefinedUsing
      (pthread.R q id)
      (primR "unsigned long" q' arg) := {}.

  Section with_cpp.
    Import rep.RepFor.
    Import RepScheme.

    Context `{Σ : cpp_logic,σ : genv,!HasStdThreads Σ}.

    #[global] Instance R_learnable :
        Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R) := ltac:(solve_learnable).

    #[global] Instance handle_learnable_1 :
      Cbn (Learn (learn_eq ==> req_eq ==> learn_eq ==> learn_hints.fin)
             pthread.handle) := ltac:(solve_learnable).

    #[global] Instance handle_learnable_2 :
      Cbn (Learn (req_eq ==> learn_eq ==> learn_eq ==> learn_hints.fin)
             pthread.handle) := ltac:(solve_learnable).

    #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
      rep.RepFor.C "pthread_t" [ArgType.CFrac; ArgType.Model _]
        R := {}.

  End with_cpp.
End pthread.
