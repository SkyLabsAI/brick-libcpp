
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.cstdlib_atoi_cpp.
Require Import skylabs.cpp.string.

Import normalize.only_provable_norm.
Import normalize.normalize_ptr.
Import refine_lib.
Import expr_join.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  #[local] Hint Resolve delayed_case.smash_delayed_case_B | 1000 : br_hints.
  #[local] Hint Resolve delayed_case.expr_join.smash_delayed_case_B | 1000 : br_hints.
  #[only(cfracsplittable)] derive cstring.R.

  cpp.spec "atoi_zero_and_no_conversion()" default.
  Lemma atoi_zero_and_no_conversion_ok :
    verify[source] "atoi_zero_and_no_conversion()".
  Proof.
    verify_spec.
    go $usenamed=true.
    go $usenamed=true.
    iExists (cQp.mk true _x_0); iFrame.
    iIntros "Hstr".
    go $usenamed=true.
    iExists (cQp.mk true _x_4); iFrame.
    iIntros "Hstr2".
    go $usenamed=true.
    all: iExists (1$c)%cQp; iFrame.
  Qed.

  cpp.spec "atoi_signed_values()" default.
  Lemma atoi_signed_values_ok :
    verify[source] "atoi_signed_values()".
  Proof.
    verify_spec.
    go $usenamed=true.
    go $usenamed=true.
    iExists (cQp.mk true _x_0); iFrame.
    iIntros "Hpositive".
    go $usenamed=true.
    iExists (cQp.mk true _x_4); iFrame.
    iIntros "Hnegative".
    go $usenamed=true.
    iExists (cQp.mk true _x_8); iFrame.
    iIntros "Hexplicit".
    go $usenamed=true.
    all: iExists (1$c)%cQp; iFrame.
  Qed.

  cpp.spec "atoi_whitespace_and_prefix()" default.
  Lemma atoi_whitespace_and_prefix_ok :
    verify[source] "atoi_whitespace_and_prefix()".
  Proof.
    verify_spec.
    go $usenamed=true.
    go $usenamed=true.
    iExists (cQp.mk true _x_0); iFrame.
    iIntros "Hwhitespace".
    go $usenamed=true.
    iExists (cQp.mk true _x_4); iFrame.
    iIntros "Hprefix".
    go $usenamed=true.
    all: iExists (1$c)%cQp; iFrame.
  Qed.

  cpp.spec "atol_decimal_value()" default.
  Lemma atol_decimal_value_ok :
    verify[source] "atol_decimal_value()".
  Proof.
    verify_spec.
    go $usenamed=true.
    go $usenamed=true.
    iExists (cQp.mk true _x_0); iFrame.
    iIntros "Hstr".
    go $usenamed=true.
    all: iExists (1$c)%cQp; iFrame.
  Qed.

  cpp.spec "atoll_wide_value()" default.
  Lemma atoll_wide_value_ok :
    verify[source] "atoll_wide_value()".
  Proof.
    verify_spec.
    go $usenamed=true.
    go $usenamed=true.
    iExists (cQp.mk true _x_0); iFrame.
    iIntros "Hstr".
    go $usenamed=true.
    all: iExists (1$c)%cQp; iFrame.
  Qed.

  #[local] Open Scope Z_scope.

  Lemma atoi_int_out_of_range_unreachable :
    valid<"int"> (atoi "2147483648") -> False.
  Proof.
    intro Hvalid.
    pose proof
      (type.has_int_type_RL int_rank.Iint Signed
         (atoi "2147483648") Hvalid) as Hbound.
    change (-2147483648 <= 2147483648 <= 2147483647)%Z in Hbound.
    Arith.arith_simpl.
    Arith.arith_solve.
  Qed.

  Lemma atol_long_out_of_range_unreachable :
    valid<"long"> (atoi "9223372036854775808") -> False.
  Proof.
    intro Hvalid.
    pose proof
      (type.has_int_type_RL int_rank.Ilong Signed
         (atoi "9223372036854775808") Hvalid) as Hbound.
    change
      (-9223372036854775808 <= 9223372036854775808 <= 9223372036854775807)%Z
      in Hbound.
    Arith.arith_simpl.
    Arith.arith_solve.
  Qed.

  Lemma atoll_long_long_out_of_range_unreachable :
    valid<"long long"> (atoi "9223372036854775808") -> False.
  Proof.
    intro Hvalid.
    pose proof
      (type.has_int_type_RL int_rank.Ilonglong Signed
         (atoi "9223372036854775808") Hvalid) as Hbound.
    change
      (-9223372036854775808 <= 9223372036854775808 <= 9223372036854775807)%Z
      in Hbound.
    Arith.arith_simpl.
    Arith.arith_solve.
  Qed.

End with_cpp.

