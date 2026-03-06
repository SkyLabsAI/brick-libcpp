(**
Tentative Specifications for <string>
*)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.auto.cpp.elpi.derive.
Require Export skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.string.inc_string_cpp.

(** TODO: split this into pred.v and spec.v *)


#[global] Notation string_type := bs (only parsing).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (* NOTE: the type `bs` is only suitable for the `char` and `char8` specializations.
     To support wider character types, we need to generalize this to something like
     `list N`
   *)
  Parameter basic_stringR :
    forall value_type : type, cQp.t -> string_type -> Rep.
  #[only(type_ptr="std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>",cfracsplittable)] derive basic_stringR.

  #[global] Instance: Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) basic_stringR) := ltac:(solve_learnable).

End with_cpp.
