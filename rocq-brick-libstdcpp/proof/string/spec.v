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

  (* Self-assignment needs only the destination resource. For a distinct
     source, preserve its contents and the exact fraction of its ownership.
     sourceShare is None for self-assignment and Some q for normal copying. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::operator=(const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" from source as string_op_eq_string_spec with (
    \this this
    \arg{other} "" (Vref other)
    \pre{s} this |-> basic_stringR "char" 1$m s
    \prepost{sourceShare otherS}
      if bool_decide (this = other) then [| otherS = s /\ sourceShare = None |]
      else Exists q, [| sourceShare = Some q |] **
        other |-> basic_stringR "char" q otherS
    \post[Vptr this]
      this |-> basic_stringR "char" 1$m otherS).

  (** <<size_type size() const noexcept;>>

      <https://eel.is/c++draft/string.capacity> -- the number of characters.
      Total: it only reads the model, so no call is undefined. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::size() const" from source as string_size_spec with (
    \this this
    \prepost{q s} this |-> basic_stringR "char" q s
    \post[Vn (N.of_nat (BS.length s))] emp).

  (** <<size_type length() const noexcept;>>

      <https://eel.is/c++draft/string.capacity> -- the same as <<size()>>.
      Total, as <<size()>>. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::length() const" from source as string_length_spec with (
    \this this
    \prepost{q s} this |-> basic_stringR "char" q s
    \post[Vn (N.of_nat (BS.length s))] emp).

  (** <<bool empty() const noexcept;>>

      <https://eel.is/c++draft/string.capacity> -- whether <<size() == 0>>.
      Total, as <<size()>>. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::empty() const" from source as string_empty_spec with (
    \this this
    \prepost{q s} this |-> basic_stringR "char" q s
    \post[Vbool (bool_decide (s = BS.EmptyString))] emp).

End with_cpp.
