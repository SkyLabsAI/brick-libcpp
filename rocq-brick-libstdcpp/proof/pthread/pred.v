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

  (** pthread_join, some error codes are returned via a void pointer. *)
  mlock
  Definition canceled `{Σ : cpp_logic,σ : genv} (p : ptr) : mpred :=
    let int_size := int_rank.bitsN int_rank.Iint in
    let addr := trim int_size (pthread_errno.to_Z pthread_errno.CANCELED) in
    pinned_ptr (Z.to_N addr) p.

  #[global] Instance learn_canceled `{Σ : cpp_logic, σ : genv} p0 p1 :
    Learnable
      (pthread.canceled p0)
      (pthread.canceled p1)
      [p0 = p1] := ltac:(solve_learnable).

  #[global]
  Instance pers_canceled `{Σ : cpp_logic, σ : genv} p : Persistent (pthread.canceled p).
  Proof. rewrite pthread.canceled.unlock /=; apply  _. Qed.

  #[global]
  Instance affine_canceled `{Σ : cpp_logic, σ : genv} p : Affine (pthread.canceled p).
  Proof. rewrite pthread.canceled.unlock /=; apply  _. Qed.

End pthread.
