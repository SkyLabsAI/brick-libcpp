(**
  Refinement-based specifications for the <iostream> library.
  See README.md for more information
*)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.

Require Import skylabs.auto.hints.kont.

Require Import skylabs.brick.libstdcpp.iostream.itree_prop.

Require Import skylabs.brick.libstdcpp.iostream.inc_iostream_cpp.

(** TODO upstream START *)
#[only(cfracsplittable)] derive cstring.R.

(** TODO upstream *)
#[global] Bind Scope bs_scope with cstring.t.
(* We only have `Bind Scope bs_scope with t.` inside `Module cstring.` *)
(** TODO upstream END *)

(** Events that send output.

    For most buffered streams, writes go to the buffer and are only guaranteed
    to be sent to the consumer on a [Flush].
 *)
Variant output_event : Set :=
  | Write (_ : N).

Variant input_event : Set :=
  | Read (_ : N).

(** The behavior of an [ostream] is described by a handler of an [output_event]  *)
Notation Ostream := (SepHandler mpred output_event).
Notation Istream := (SepHandler mpred input_event).

Module ostream.
  Parameter gname : Set.

  (** TODO: Add support for <iomanip> *)
  Parameter R : forall `{Σ : cpp_logic} {σ : genv}, Ostream -> gname -> cQp.t -> Rep.
  #[only(cfracsplittable)] derive R.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    #[global] Instance: Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

  End with_cpp.
End ostream.

Module istream.
  Parameter gname : Set.
  Parameter R : forall `{Σ : cpp_logic} {σ : genv}, Istream -> gname -> cQp.t -> Rep.
  #[only(cfracsplittable)] derive R.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    #[global] Instance: Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

  End with_cpp.

End istream.
