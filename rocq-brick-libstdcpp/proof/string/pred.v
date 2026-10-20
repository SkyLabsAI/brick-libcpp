(**
Tentative Specifications for <string>
*)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.auto.cpp.elpi.derive.
Require Import skylabs.auto.cpp.hints.const.
Require Export skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.string.inc_string_cpp.

(**
Model of basic_string<char>/basic_string<char8>.

NOTE: the type `bs` is only suitable for the `char` and `char8` specializations.

To support wider character types, we need to generalize this to something like `list N` or
`list PrimInt63`.
*)
#[global] Abbreviation string_type := bs (only parsing).

Parameter basic_stringR :
  forall `{Σ : cpp_logic} {σ : genv} (value_type : type), cQp.t -> string_type -> Rep.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[only(type_ptr="std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>",cfracsplittable)] derive basic_stringR.

  #[global] Instance: Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) basic_stringR) := ltac:(solve_learnable).

  (** Const-qualification of a <<std::string>>: [wp_make_const] and
      [wp_make_mutable] at a <<const std::string>> local move the [cQp.t] and
      change nothing else.

      An axiom, since [basic_stringR] is abstract: [wp_const] at a class
      descends into its fields, which [basic_stringR] does not expose. It is
      [const.CONST1] at this library's translation unit, so it holds only at
      full ownership and only in clients whose type table contains this one's. *)
  Axiom basic_stringR_const :
    const.CONST1 source "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>" (basic_stringR "char").
  Definition basic_stringR_const_C := [CANCEL] basic_stringR_const.

End with_cpp.

#[global] Hint Resolve basic_stringR_const_C : br_hints.
