(**
Tentative Specifications for <string>
*)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.string.pred.

Require Import skylabs.brick.libstdcpp.string.inc_string_cpp.

(** The static member <<npos>>, <<size_type(-1)>>
    (<https://eel.is/c++draft/basic.string.general>). Clients that read it
    own a fraction of it, as with [std.compare.strong_ordering_globals]. *)
#[global] Abbreviation string_npos_global q :=
  (_global "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::npos" |-> primR "unsigned long" q (Vn (N.ones 64))).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition N_to_byte (n : N) : Byte.byte :=
    match Byte.of_N n with
    | None => Byte.x00 (* TODO: default *)
    | Some b => b
    end.

  (** [string_find c pos s] is the first index at or after [pos] that holds [c]
      in [s], if any. *)
  Fixpoint string_find_from (c : Byte.byte) (i : nat) (s : bs) : option nat :=
    match s with
    | BS.EmptyString => None
    | BS.String b s' => if bool_decide (b = c) then Some i else string_find_from c (S i) s'
    end.
  Definition string_find (c : Byte.byte) (pos : nat) (s : bs) : option nat :=
    string_find_from c pos (BS.substring pos (BS.length s) s).

  (** [string_erase pos n s] removes from [s] the [min n (length s - pos)]
      characters that start at [pos]. *)
  Definition string_erase (pos n : N) (s : bs) : bs :=
    let len := N.of_nat (BS.length s) in
    let rlen := N.min n (len - pos) in
    BS.append (BS.substring 0 (N.to_nat pos) s)
      (BS.substring (N.to_nat (pos + rlen)) (BS.length s) s).

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

  (** <<size_type find(char c, size_type pos = 0) const noexcept;>>

      <https://eel.is/c++draft/string.find> -- the first index at or after
      [pos] that holds [c], or <<npos>>. A [pos] past the end finds nothing.
      Total: no call is undefined. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::find(char, unsigned long) const" from source as string_find_char_spec with (
    \this this
    \arg{c} "" (Vchar c)
    \arg{pos} "" (Vn pos)
    \prepost{q s} this |-> basic_stringR "char" q s
    \post[Vn (match string_find (N_to_byte c) (N.to_nat pos) s with
               | Some i => N.of_nat i
               | None => N.ones 64
               end)] emp).

  (** <<void push_back(char c);>>

      <https://eel.is/c++draft/string.modifiers> -- appends [c]. It is
      non-const, so it needs the whole string. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::push_back(char)" from source as string_push_back_spec with (
    \this this
    \arg{c} "" (Vchar c)
    \pre{s} this |-> basic_stringR "char" 1$m s
    \post this |-> basic_stringR "char" 1$m (BS.append s (BS.String (N_to_byte c) BS.EmptyString))).

  (** <<basic_string& operator+=(char c);>>

      <https://eel.is/c++draft/string.op.append> -- the same as
      <<push_back(c)>>; returns <<*this>>. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::operator+=(char)" from source as string_op_plus_eq_char_spec with (
    \this this
    \arg{c} "" (Vchar c)
    \pre{s} this |-> basic_stringR "char" 1$m s
    \post[Vptr this] this |-> basic_stringR "char" 1$m (BS.append s (BS.String (N_to_byte c) BS.EmptyString))).

  (** <<basic_string& erase(size_type pos = 0, size_type n = npos);>>

      <https://eel.is/c++draft/string.erase> -- removes the
      <<min(n, size() - pos)>> characters that start at [pos]; returns
      <<*this>>. A [pos] past the end throws <<out_of_range>>, which is not
      undefined; since exceptions are not modeled, the spec requires
      <<pos <= size()>>. *)
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::erase(unsigned long, unsigned long)" from source as string_erase_spec with (
    \this this
    \arg{pos} "" (Vn pos)
    \arg{n} "" (Vn n)
    \pre{s} this |-> basic_stringR "char" 1$m s
    \require (pos <= N.of_nat (BS.length s))%N
    \post[Vptr this] this |-> basic_stringR "char" 1$m (string_erase pos n s)).

End with_cpp.
