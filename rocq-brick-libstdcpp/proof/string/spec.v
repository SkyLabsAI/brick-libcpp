(**
Tentative Specifications for <string>
*)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.string.pred.

Require Import skylabs.brick.libstdcpp.string.inc_string_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition N_to_byte (n : N) : Byte.byte :=
    match Byte.of_N n with
    | None => Byte.x00 (* TODO: default *)
    | Some b => b
    end.

  (* default constructor *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::basic_string()" from source as string_default_ctor_spec with (
    \this this
    \post this |-> basic_stringR "char" 1$m "").

  (* default destructor *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::~basic_string()" from source as string_dtor_spec with (
     \this this
     \pre{s} this |-> basic_stringR "char" 1$m s
     \post emp).

  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::operator=(char)" from source as string_op_eq_char_spec with (
    \this this
    \arg{c} "" (Vchar c)
    \pre{s} this |-> basic_stringR "char" 1$m s
    \post[Vptr this]
      this |-> basic_stringR "char" 1$m (BS.String (N_to_byte c) BS.EmptyString)).

  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::operator=(const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" from source as string_op_eq_string_spec with (
    \this this
    \arg{other} "" (Vref other)
    \pre{s} this |-> basic_stringR "char" 1$m s
    \prepost{otherS} other |-> basic_stringR "char" 1$m otherS
    \post[Vptr this]
      this |-> basic_stringR "char" 1$m otherS).

End with_cpp.
