
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cctype.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.cctype_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "test_alphanumeric_classes()" default.
  Lemma test_alphanumeric_classes_ok : verify[source] "test_alphanumeric_classes()".
  Proof.

    verify_spec.

    go $usenamed=true.

    all: go $usenamed=true.

    all: iExists 1%cQp; go $usenamed=true.

  Qed.

  cpp.spec "test_space_and_case_classes()" default.
  Lemma test_space_and_case_classes_ok : verify[source] "test_space_and_case_classes()".
  Proof.
    verify_spec.
    go $usenamed=true.
    all: iExists 1%cQp; go $usenamed=true.
  Qed.

  cpp.spec "test_printing_classes()" default.
  Lemma test_printing_classes_ok : verify[source] "test_printing_classes()".
  Proof.
    verify_spec.
    go $usenamed=true.
    all: iExists 1%cQp; go $usenamed=true.
  Qed.

  cpp.spec "test_case_conversion()" default.
  Lemma test_case_conversion_ok : verify[source] "test_case_conversion()".
  Proof.
    verify_spec.
    go $usenamed=true.
    all: iExists 1%cQp; go $usenamed=true.
  Qed.

  cpp.spec "test_eof_cases()" default.
  Lemma test_eof_cases_ok : verify[source] "test_eof_cases()".
  Proof.
    verify_spec.
    go $usenamed=true.
    all: iExists 1%cQp; go $usenamed=true.
  Qed.

  Definition uchar_of_char (c : N) : Z := Z.of_N c.

  cpp.spec "safe_isalpha(char)" with
    (\arg{ch} "ch" (Vchar ch)
     \post[Vbool (isalpha (uchar_of_char ch))] emp).
  Lemma safe_isalpha_ok : verify[source] "safe_isalpha(char)".
  Proof.

    verify_spec.

    go $usenamed=true.

    all: iExists 1%cQp; go $usenamed=true.
  Qed.

  Definition canonical_hex_result (c : N) : Z :=
    if isxdigit (uchar_of_char c)
    then toupper (uchar_of_char c)
    else (-1)%Z.

  cpp.spec "canonical_hex(char)" with
    (\arg{ch} "ch" (Vchar ch)
     \post[Vint (canonical_hex_result ch)] emp).
  Lemma canonical_hex_ok : verify[source] "canonical_hex(char)".
  Proof.

    verify_spec.

    go $usenamed=true.

    1-3: iExists 1%cQp; go $usenamed=true.

    wp_if.

    all: intros; go $usenamed=true.

    2: iExists 1%cQp; go $usenamed=true.

    all: unfold canonical_hex_result, uchar_of_char; rewrite <- H; go $usenamed=true.

    case_bool_decide; go $usenamed=true.
  Qed.

  cpp.spec "test_realistic_composition()" default.
  Lemma test_realistic_composition_ok : verify[source] "test_realistic_composition()".
  Proof.
    verify_spec.
    go $usenamed=true.
    all: iExists 1%cQp; go $usenamed=true.
  Qed.

  cpp.spec "main()" default.
  Lemma main_ok : verify[source] "main()".
  Proof.
    verify_spec.
    go $usenamed=true.

  Qed.

End with_cpp.

Lemma negative_two_is_outside_cctype_domain {σ : genv} :
  ¬ VALID (σ := σ) (-2)%Z.
Proof.
  rewrite VALID.unlock.

  intros [H | H].
  - pose proof (type.has_int_type_RL int_rank.Ichar Unsigned (-2)%Z H) as Hb.
    change (0 <= (-2) <= 255)%Z in Hb. lia.
  - lia.
Qed.
