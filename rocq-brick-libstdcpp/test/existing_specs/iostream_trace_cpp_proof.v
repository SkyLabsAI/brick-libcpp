
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream_trace.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.iostream_trace_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : iostream_trace_cpp.source ⊧ σ}.

  cpp.spec "trace_insert_c_string(std::basic_ostream<char, std::char_traits<char>>&)" as trace_insert_c_string_exact_spec from source with (
    \arg{out} "out" (Vptr out)
    \pre{osM str} out |-> ostreamR 1$m osM ** out |-> ostream_contentR 1$m str
    \post[Vbool true] out |-> ostreamR 1$m osM **
      out |-> ostream_contentR 1$m (str ++ "trace")%bs
  ).

  Lemma trace_insert_c_string_ok :
    verify[source] "trace_insert_c_string(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.
  Qed.

  cpp.spec "trace_insert_int(std::basic_ostream<char, std::char_traits<char>>&)" as trace_insert_int_exact_spec from source with (
    \arg{out} "out" (Vptr out)
    \pre{osM str} out |-> ostreamR 1$m osM ** out |-> ostream_contentR 1$m str
    \post[Vbool true] out |-> ostreamR 1$m osM **
      out |-> ostream_contentR 1$m (str ++ Z_to_string (-17))
  ).

  Lemma trace_insert_int_ok :
    verify[source] "trace_insert_int(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.
  Qed.

  cpp.spec "trace_insert_unsigned_long(std::basic_ostream<char, std::char_traits<char>>&)" as trace_insert_unsigned_long_exact_spec from source with (
    \arg{out} "out" (Vptr out)
    \pre{osM str} out |-> ostreamR 1$m osM ** out |-> ostream_contentR 1$m str
    \post[Vbool true] out |-> ostreamR 1$m osM **
      out |-> ostream_contentR 1$m (str ++ Z_to_string 42)
  ).

  Lemma trace_insert_unsigned_long_ok :
    verify[source] "trace_insert_unsigned_long(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.
  Qed.

  cpp.spec "trace_apply_endl(std::basic_ostream<char, std::char_traits<char>>&)" as trace_apply_endl_exact_spec from source with (
    \arg{out} "out" (Vptr out)
    \pre{osM str} out |-> ostreamR 1$m osM ** out |-> ostream_contentR 1$m str
    \post[Vbool true] out |-> ostreamR 1$m osM **
      out |-> ostream_contentR 1$m (str ++ "\n")%bs
  ).

  Lemma trace_apply_endl_ok :
    verify[source] "trace_apply_endl(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.
  Qed.

  cpp.spec "trace_insert_endl_manipulator(std::basic_ostream<char, std::char_traits<char>>&)" as trace_insert_endl_manipulator_exact_spec from source with (
    \arg{out} "out" (Vptr out)
    \pre{osM str} out |-> ostreamR 1$m osM ** out |-> ostream_contentR 1$m str
    \post[Vbool true] out |-> ostreamR 1$m osM **
      out |-> ostream_contentR 1$m (str ++ "\n")%bs
  ).

  Lemma trace_insert_endl_manipulator_ok :
    verify[source] "trace_insert_endl_manipulator(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.

    iExists (fun x => x), (fun str0 => (str0 ++ "\n")%bs).
    go $usenamed=true.
  Qed.

  cpp.spec "trace_take_int(std::basic_istream<char, std::char_traits<char>>&, int&)" as trace_take_int_identity_spec from source with (
    \arg{inP} "in" (Vptr inP)
    \arg{valueP} "value" (Vptr valueP)
    \pre{isM} inP |-> istreamR 1$m isM
    \pre valueP |-> anyR "int" 1$m
    \post[Vbool true] Exists isM' n,
      inP |-> istreamR 1$m isM' ** valueP |-> intR 1$m n
  ).

  Lemma trace_take_int_ok :
    verify[source] "trace_take_int(std::basic_istream<char, std::char_traits<char>>&, int&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.
  Qed.

  cpp.spec "trace_output_composition(std::basic_ostream<char, std::char_traits<char>>&)" as trace_output_composition_exact_spec from source with (
    \arg{out} "out" (Vptr out)
    \pre{osM str} out |-> ostreamR 1$m osM ** out |-> ostream_contentR 1$m str
    \post[Vbool true] out |-> ostreamR 1$m osM **
      out |-> ostream_contentR 1$m
        ((((str ++ "trace=") ++ Z_to_string (-17)) ++ Z_to_string 42) ++ "\n")%bs
  ).

  Lemma trace_output_composition_ok :
    verify[source] "trace_output_composition(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec; go $usenamed=true.
    iExists (fun x => x), (fun str0 => (str0 ++ "\n")%bs).
    go $usenamed=true.
  Qed.

  (* Keep both same-binding families live for the duplicate-selection check. *)
  Require Import skylabs.brick.libstdcpp.iostream.spec.

  #[local] Remove Hints ostream.ostream_insert_spec_spec_instance ostream.ostream_print_int_spec_spec_instance ostream.ostream_print_ulong_spec_spec_instance ostream.endl_spec_spec_instance ostream.ostream_insert_string_spec_spec_instance istream.istream_take_int_spec_spec_instance : typeclass_instances.

Lemma trace_output_composition_duplicate_selection_ok : denoteModule source ⊢ ▷ endl_spec ∗ ▷ ostream_insert_spec ∗ ▷ ostream_insert_string_spec ∗ ▷ ostream_print_int_spec ∗ ▷ ostream_print_ulong_spec -∗ trace_output_composition_exact_spec.

Proof.

verify_spec; go $usenamed=true.

iExists (fun x => x), (fun str0 => (str0 ++ "\n")%bs).

go $usenamed=true.

Qed.

Lemma trace_insert_c_string_null_unreachable (q : cQp.t) (str : cstring.t) : nullptr |-> cstring.R q str ⊢ False.

Proof.

exact (nullptr_at_cstringR_contra q str).

Qed.

End with_cpp.


