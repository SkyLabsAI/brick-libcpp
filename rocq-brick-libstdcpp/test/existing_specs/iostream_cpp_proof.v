
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.iostream_cpp.

Require Import skylabs.brick.libstdcpp.cassert.spec.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : source ⊧ σ}.

  cpp.spec "test_ostream_int(std::basic_ostream<char, std::char_traits<char>>&)"
    as test_ostream_int_spec from source with (
    \arg{out} "out" (Vptr out)
    \prepost{OS γ} out |-> ostream.R OS γ 1$m
    \pre{Q} ostream.bs_dos OS (ostream.format_int (-27)) Q
    \post Q).

  Lemma test_ostream_int_ok :
    verify[source] "test_ostream_int(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec.

    go $usenamed=true.
    Arith.arith_simpl.

    wapply ((ostream.bs_dos_proper_frame OS (ostream.format_int (-27))).(kont._frame) Q).

    go $usenamed=true.

iSplitL.

2: go $usenamed=true.

2: iFrame.

iIntros ([]) "HQ".

cbn.

go $usenamed=true.

Qed.

  cpp.spec "test_ostream_unsigned_long(std::basic_ostream<char, std::char_traits<char>>&)"
    as test_ostream_unsigned_long_spec from source with (
    \arg{out} "out" (Vptr out)
    \prepost{OS γ} out |-> ostream.R OS γ 1$m
    \pre{Q} ostream.bs_dos OS (ostream.format_int 42) Q
    \post Q).

  Lemma test_ostream_unsigned_long_ok :
    verify[source] "test_ostream_unsigned_long(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
    Arith.arith_simpl.
    wapply ((ostream.bs_dos_proper_frame OS (ostream.format_int 42)).(kont._frame) Q).
    go $usenamed=true.
    iSplitL.
    2: go $usenamed=true.
    2: iFrame.
    iIntros ([]) "HQ".
    cbn.
    go $usenamed=true.
  Qed.

  cpp.spec "test_endl_direct(std::basic_ostream<char, std::char_traits<char>>&)"
    as test_endl_direct_spec from source with (
    \arg{out} "out" (Vptr out)
    \prepost{OS γ} out |-> ostream.R OS γ 1$m
    \pre{Q} ostream.bs_dos OS (BS.String Byte.x0a BS.EmptyString) Q
    \post Q).

  Lemma test_endl_direct_ok :
    verify[source] "test_endl_direct(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
    Arith.arith_simpl.

iExists Q.

iFrame.

go $usenamed=true.

Qed.

  cpp.spec "test_ostream_c_string(std::basic_ostream<char, std::char_traits<char>>&, const char*)"
    as test_ostream_c_string_spec from source with (
    \arg{out} "out" (Vptr out)
    \prepost{OS γ} out |-> ostream.R OS γ 1$m
    \arg{text} "text" (Vptr text)
    \prepost{q__s strM} text |-> cstring.R q__s strM
    \pre{Q} ostream.bs_dos OS strM Q
    \post Q).

  Lemma test_ostream_c_string_ok :
    verify[source] "test_ostream_c_string(std::basic_ostream<char, std::char_traits<char>>&, const char*)".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
    Arith.arith_simpl.

wapply ((ostream.bs_dos_proper_frame OS strM).(kont._frame) Q).

    go $usenamed=true.
    iSplitL.
    2: go $usenamed=true.
    2: iFrame.
    iIntros ([]) "HQ".
    cbn.
    go $usenamed=true.
  Qed.

  cpp.spec "test_endl_manipulator_overload(std::basic_ostream<char, std::char_traits<char>>&)"
    as test_endl_manipulator_overload_spec from source with (
    \arg{out} "out" (Vptr out)
    \prepost{OS γ} out |-> ostream.R OS γ 1$m
    \pre{Q} ostream.bs_dos OS (BS.String Byte.x0a BS.EmptyString) Q
    \post Q).

  Lemma test_endl_manipulator_overload_ok :
    verify[source] "test_endl_manipulator_overload(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
    Arith.arith_simpl.

iExists _, _.

iFrame.

iDestruct select (ostream.endl_spec) as "#Hendl".

iEval (rewrite /ostream.endl_spec /specify) in "Hendl".

iFrame "Hendl".

go $usenamed=true.

iExists Q.

iFrame.

iSplitR.

go $usenamed=true.

go $usenamed=true.

Qed.

  cpp.spec "test_output_composition(std::basic_ostream<char, std::char_traits<char>>&)"
    as test_output_composition_spec from source with (
    \arg{out} "out" (Vptr out)
    \prepost{OS γ} out |-> ostream.R OS γ 1$m
    \pre{Q}
      ostream.bs_dos OS ("value="%bs)
        (ostream.bs_dos OS (ostream.format_int (-27))
          (ostream.bs_dos OS (ostream.format_int 42)
            (ostream.bs_dos OS (BS.String Byte.x0a BS.EmptyString) Q)))
    \post Q).

  Lemma test_output_composition_ok :
    verify[source] "test_output_composition(std::basic_ostream<char, std::char_traits<char>>&)".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
    Arith.arith_simpl.

iExists (ostream.bs_dos OS (ostream.format_int (-27)) (ostream.bs_dos OS (ostream.format_int 42) (ostream.bs_dos OS (BS.String Byte.x0a BS.EmptyString) Q))).

iFrame.

go $usenamed=true.

Arith.arith_simpl.

wapply ((ostream.bs_dos_proper_frame OS (ostream.format_int (-27))).(kont._frame) (ostream.bs_dos OS (ostream.format_int 42) (ostream.bs_dos OS (BS.String Byte.x0a BS.EmptyString) Q))).

    go $usenamed=true.
    iSplitL.
    2: go $usenamed=true.
    2: iFrame.
    iIntros ([]) "HQ".
    cbn.
    go $usenamed=true.

wapply ((ostream.bs_dos_proper_frame OS (ostream.format_int 42)).(kont._frame) (ostream.bs_dos OS (BS.String Byte.x0a BS.EmptyString) Q)).

    go $usenamed=true.
    iSplitL.
    2: go $usenamed=true.
    2: iFrame.
    iIntros ([]) "HQ".
    cbn.
    go $usenamed=true.

    iExists _, _.
    iDestruct select (ostream.endl_spec) as "#Hendl".
    iEval (rewrite /ostream.endl_spec /specify) in "Hendl".
    iFrame "Hendl".
    go $usenamed=true.
    iExists Q.
    iFrame.
    iSplitR.
    go $usenamed=true.
    go $usenamed=true.
  Qed.

  Lemma iostream_c_string_null_unreachable (q : cQp.t) (str : cstring.t) :
    nullptr |-> cstring.R q str ⊢ False.
  Proof.
    exact (nullptr_at_cstringR_contra q str).
  Qed.

End with_cpp.
