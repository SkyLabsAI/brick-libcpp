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

(* UPSTREAM *)
#[global] Hint Extern 0 (CFractional (fun q => match ?x with | _ => _ end)) =>
  destruct x : typeclass_instances.

cpp.enum "pthread_errno" from source variant.

Module pthread_attr.

  (** cpp.class does not support unions *)
  (* cpp.class "pthread_attr_t" prefix "" from source dataclass. *)

  Variant T := Bytes (_ : list N) | Align (_ : Z).

  Parameter default : T.

  Definition selector (x : option T) : option nat :=
    match x with
    | None | Some (Bytes _) => Some 0%nat
    | Some (Align _) => Some 1%nat
    end.

  mlock
  Definition R `{Σ : cpp_logic, σ : genv} (q : cQp.t) (x : option T) : Rep :=
    match x with
    | None =>
        ∃ xs, _field "__size"%cpp_name |-> array_sliceR "char" 0 56 (fun x => charR q x) xs
    | Some (Bytes xs) =>
        _field "__size"%cpp_name |-> array_sliceR "char" 0 56 (fun x => charR q x) xs
    | Some (Align n) =>
        _field "__align"%cpp_name |-> longR q n
    end ∗
    unionR "pthread_attr_t" q (selector x) .
  #[only(cfractional,cfracvalid,ascfractional,type_ptr,lazy_unfold)] derive R.

Section with_cpp.
  Import rep.RepFor.
  Import RepScheme.

  Context `{Σ : cpp_logic,σ : genv}.

  #[global] Instance R_learnable :
      Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) R) := ltac:(solve_learnable).

  #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
    rep.RepFor.C "pthread_attr_t" [ArgType.CFrac; ArgType.Model _]
      R := {}.

End with_cpp.
End pthread_attr.

Module pthread.
  Import auto.telescopes auto.telescopes.TeleNotations.

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

Section with_cpp.
  Import rep.RepFor.
  Import RepScheme.

  Context `{Σ : cpp_logic,σ : genv,!HasStdThreads Σ}.

  #[global] Instance R_learnable :
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R) := ltac:(solve_learnable).


  Definition learn_eq_dep {T U V} : Learning V → Learning (forall x : T, U x → V) :=
    fun '{|unLearning := k|} =>
      {|unLearning := fun L R ls => forall a a' b b', k (L a b) (R a' b') ((existT a b = existT a' b') :: ls) |}.

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
