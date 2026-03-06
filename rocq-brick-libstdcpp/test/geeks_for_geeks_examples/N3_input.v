Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.
Require Import skylabs.brick.libstdcpp.string.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N3_input_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.


  cpp.spec "main()" from source as main_spec with (
    \pre{isM} _global "std::cin" |-> istreamR 1$m isM
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      (* TODO: this is not precise enough *)
      Exists n isM',
        _global "std::cin" |-> istreamR 1$m isM' **
        _global "std::cout" |-> ostream_contentR 1$m (str ++ Z_to_string n)
      ).

  Eval vm_compute in fst <$> NM.elements source.(symbols).

  (*
  cpp.spec
    "std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"
    from source as istream_take_char_spec with (
        (* cpp.spec "std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" from source with ( *)
        \arg{isP} "" (Vptr isP)
          \pre{isM} isP |-> istreamR 1$m isM
          \arg{strP} "" (Vptr strP)
          \pre{strM} strP |-> basic_stringR "char" 1$m strM
          \post[Vptr isP]
          Exists isM' strM',
        isP |-> istreamR 1$m isM' **
          strP |-> basic_stringR "char" 1$m strM' (* TODO: this is not precise enough *)
      ).
*)



  (* cpp.spec "std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" from source as istream_input_string with *)

  (*
  cpp.spec "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::basic_string()" from source as string_ctor_spec with (
    \this this
    \post this |-> cppStringR 1$m "").

  #[global] Declare Instance cppStringR_typed : Typed2 "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>" cppStringR.
*)
  #[global] Declare Instance basic_stringR_typed : Typed2 "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>" (basic_stringR "char").


  Lemma main_ok : verify?[source] main_spec.
  Proof.
    verify_spec; go.
    (* progress ework with br_erefl. *)
    set name := "std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name.
    exfalso.
    clear.
Set Printing All.
Check "std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name.
Eval cbv in ("std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name).
(* Print "std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name. *)

  Qed.
(* Print "std::operator() <char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name. *)

  (* #[ignore_missing] *)
  Print istream_take_char_spec .


(* The following dependencies are missing specifications:
"std::cin"%cpp_name
"std::cout"%cpp_name
"std::basic_istream<char, std::char_traits<char>>::operator>>(int&)"%cpp_name
"std::basic_ostream<char, std::char_traits<char>>::operator<<(int)"%cpp_name *)

  (* Print _inststd_dot__opgreatergreater_with_and_cons_ref_named_inststd_dot_basic__istream_with_cons_char_cons_named_inststd_dot_char__traits_with_cons_char_nil_nil_cons_ref_named_inststd_dot_____cxx11_dot_basic__string_with_cons_char_cons_named_inststd_dot_char__traits_with_cons_char_nil_cons_named_inststd_dot_allocator_with_cons_char_nil_nil_nil_with_cons_char_cons_named_inststd_dot_char__traits_with_cons_char_nil_cons_named_inststd_dot_allocator_with_cons_char_nil_nil_spec. *)
(* The following dependencies are missing specifications:
"std::endl<char, std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&)"%cpp_name
"std::cin"%cpp_name
"std::cout"%cpp_name

"std::operator>><char, std::char_traits<char>, std::allocator<char>>(std::basic_istream<char, std::char_traits<char>>&, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name
"std::operator<<<char, std::char_traits<char>, std::allocator<char>>(std::basic_ostream<char, std::char_traits<char>>&, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)"%cpp_name
"std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>::~basic_string()"%cpp_name
"std::basic_ostream<char, std::char_traits<char>>::operator<<(std::basic_ostream<char, std::char_traits<char>>&(*)(std::basic_ostream<char, std::char_traits<char>>&))"%cpp_name
"std::basic_istream<char, std::char_traits<char>>::operator>>(int&)"%cpp_name
"std::basic_ostream<char, std::char_traits<char>>::operator<<(int)"%cpp_name *)


End with_cpp.

