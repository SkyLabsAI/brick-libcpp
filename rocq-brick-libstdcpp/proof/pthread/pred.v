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

  (** [handle γ spawner tid P Pc] is a token returned when thread creation succeeds. [P] and [Pc]
      are respectively the postcondition of the thread and its cancelation postcondition. [handle]
      can be given to <<pthread_join>> to retrieve ownership of left by a thread's termination. It
      can also be given to <<pthread_cancel>> to retrieve resources from the aborted thread.

      [handle] also specifies the thread id of the spawning thread so that the precondition of [pthread_join]
      can rule out two threads trying to mutually join with each other.  *)
  Parameter handle : forall `{Σ : cpp_logic,!HasStdThreads Σ}
                       (γ : gname) (spawner tid : thread_idT)
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

  (** A local Linux/glibc thread context, for proofs that use zero as a
      pthread_t sentinel. glibc's pthread_self returns a nonzero live
      descriptor address. This persistent resource restricts the current
      thread context; it makes no assertion about every index in the generic
      HasStdThreads model, which deliberately also permits the wrapped ID zero.
      Nonzero stale words need not denote live threads. *)
  Definition linux_thread_context `{Σ : cpp_logic, !HasStdThreads Σ} : mpred :=
    ∃ th, current_thread th ** [| unwrapN th <> 0%N |].
  #[global] Hint Opaque linux_thread_context : sl_opacity typeclass_instances.
  #[global] Instance linux_thread_context_persistent
      `{Σ : cpp_logic, !HasStdThreads Σ} : Persistent linux_thread_context.
  Proof. rewrite /linux_thread_context. apply _. Qed.

  Lemma linux_thread_context_intro `{Σ : cpp_logic, !HasStdThreads Σ} th :
    current_thread th ** [| unwrapN th <> 0%N |] |-- linux_thread_context.
  Proof. rewrite /linux_thread_context. iIntros "[Hth Hnonzero]". iExists th. iFrame. Qed.

  Lemma linux_thread_context_nonzero `{Σ : cpp_logic, !HasStdThreads Σ} th :
    current_thread th ** linux_thread_context |-- [| unwrapN th <> 0%N |].
  Proof.
    rewrite /linux_thread_context. iIntros "[Hth Hcontext]".
    iDestruct "Hcontext" as (id) "[Hid %Hnonzero]".
    iDestruct (observe_2 [| id = th |] with "Hid Hth") as %->. done.
  Qed.

  Section with_cpp.
    Import rep.RepFor.
    Import RepScheme.

    Context `{Σ : cpp_logic,σ : genv,!HasStdThreads Σ}.

    #[global] Instance R_learnable :
        Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R) := ltac:(solve_learnable).

    #[global] Instance handle_learnable_1 :
      Cbn (Learn (learn_eq ==> learn_eq ==> req_eq ==> learn_eq ==> learn_hints.fin)
             pthread.handle) := ltac:(solve_learnable).

    #[global] Instance handle_learnable_2 :
      Cbn (Learn (req_eq ==> learn_eq ==> learn_eq ==> learn_eq ==> learn_hints.fin)
             pthread.handle) := ltac:(solve_learnable).

    #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
      rep.RepFor.C "pthread_t" [ArgType.CFrac; ArgType.Model _]
        R := {}.

  End with_cpp.
End pthread.
