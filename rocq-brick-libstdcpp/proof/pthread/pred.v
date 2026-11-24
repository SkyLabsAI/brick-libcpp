(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Export skylabs.brick.libstdcpp.runtime.objective.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.weakly_objective.

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

  (** A [handle] can move to any thread of the same process, if its payload can
      (SkyLabsAI/brick-libcpp#259). POSIX lets any thread of the process join a joinable
      thread, once.

      Soundness. The handle's meaning does not depend on the current thread:
      - <<pthread_join>> does not mention the current thread, and [handle] records no spawner.
      - Joining at most once is ensured because <<pthread_join>> consumes the handle, whether it
        succeeds or fails.
      - Join cycles, now possible since handles move, are not ruled out by thread ids. Instead,
        <<pthread_join>> may fail (<<EDEADLK>>), losing the handle, or block forever, which
        partial correctness allows.
      - The payload is the only part of the handle tied to a thread. <<pthread_join>> delivers
        [P], produced by the joined thread, in the joining thread, so <<pthread_create>>
        requires [LocalWith procTI] of it. The premise keeps this principle to such payloads:
        a handle for a thread-specific [P], such as [current_thread th], stays where it is.
      - The handle's [tid] is a [pthread_t], meaningful only within its process, so the
        handle can move only within that process ([procTI]).

      There is no variant with premise [WeaklyObjective P]. Invariants and mutexes need
      [WeaklyObjective (handle γ tid P)], which [handle_weakly_objective] derives from this
      axiom for [LocalWith procTI] payloads. Since <<pthread_create>> requires
      [LocalWith procTI] of the thread's postcondition, those are all the handles a client can
      obtain, so a [WeaklyObjective] premise would extend the trusted base without serving any
      of them. *)
  #[global] Axiom handle_local_with :
    ∀ `{Σ : cpp_logic, !HasStdThreads Σ} (γ : gname) (tid : thread_idT) (P : mpred),
      LocalWith procTI P → LocalWith procTI (handle γ tid P).
  #[global] Existing Instance handle_local_with.

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

    (** Handles can be kept in invariants and mutexes. [WeaklyObjective] relates indices
        ordered by [⊑], which share their process since [procTI] is monotone and process ids
        are ordered by equality. *)
    #[global] Instance handle_weakly_objective γ tid (P : mpred) :
      LocalWith procTI P → WeaklyObjective (handle γ tid P).
    Proof.
      intros HP i j Hji. apply: (local_with procTI (handle γ tid P)).
      symmetry. exact: (mlens_get_mono procTI _ _ Hji).
    Qed.

    #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
      rep.RepFor.C "pthread_t" [ArgType.CFrac; ArgType.Model _]
        R := {}.

  End with_cpp.
End pthread.
