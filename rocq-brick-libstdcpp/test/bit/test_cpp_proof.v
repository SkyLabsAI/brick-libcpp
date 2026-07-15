Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.bit.spec.
Require Import skylabs.brick.libstdcpp.test.bit.test_cpp.

#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "use_popcount(unsigned int)" as use_popcount_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (popcount (Z.to_N x))] emp).
  Lemma use_popcount_ok : verify[source] "use_popcount(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_countl_zero(unsigned int)" as use_countl_zero_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (countl_zero (Z.to_N x))] emp).
  Lemma use_countl_zero_ok : verify[source] "use_countl_zero(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_countr_zero(unsigned int)" as use_countr_zero_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (countr_zero (Z.to_N x))] emp).
  Lemma use_countr_zero_ok : verify[source] "use_countr_zero(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_countl_one(unsigned int)" as use_countl_one_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (countl_one (Z.to_N x))] emp).
  Lemma use_countl_one_ok : verify[source] "use_countl_one(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_countr_one(unsigned int)" as use_countr_one_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (countr_one (Z.to_N x))] emp).
  Lemma use_countr_one_ok : verify[source] "use_countr_one(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_bit_width(unsigned int)" as use_bit_width_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (bit_width (Z.to_N x))] emp).
  Lemma use_bit_width_ok : verify[source] "use_bit_width(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_bit_ceil(unsigned int)" as use_bit_ceil_spec from source with (
    \arg{x} "x" (Vint x)
    \require (0 <= x <= Z.of_N uint32_high_bit)
    \post[Vint (Z.of_N (bit_ceil (Z.to_N x)))] emp).
  Lemma use_bit_ceil_ok : verify[source] "use_bit_ceil(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_bit_floor(unsigned int)" as use_bit_floor_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vint (Z.of_N (bit_floor (Z.to_N x)))] emp).
  Lemma use_bit_floor_ok : verify[source] "use_bit_floor(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_has_single_bit(unsigned int)" as use_has_single_bit_spec from source with (
    \arg{x} "x" (Vint x)
    \post[Vbool (has_single_bit (Z.to_N x))] emp).
  Lemma use_has_single_bit_ok : verify[source] "use_has_single_bit(unsigned int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_rotl(unsigned int, int)" as use_rotl_spec from source with (
    \arg{x} "x" (Vint x)
    \arg{s} "s" (Vint s)
    \post[Vint (Z.of_N (rotl (Z.to_N x) s))] emp).
  Lemma use_rotl_ok : verify[source] "use_rotl(unsigned int, int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "use_rotr(unsigned int, int)" as use_rotr_spec from source with (
    \arg{x} "x" (Vint x)
    \arg{s} "s" (Vint s)
    \post[Vint (Z.of_N (rotr (Z.to_N x) s))] emp).
  Lemma use_rotr_ok : verify[source] "use_rotr(unsigned int, int)".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_bit_count_oracles()" as test_bit_count_oracles_spec
    from source with (\post emp).
  Lemma test_bit_count_oracles_ok : verify[source] "test_bit_count_oracles()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_bit_power_oracles()" as test_bit_power_oracles_spec
    from source with (\post emp).
  Lemma test_bit_power_oracles_ok : verify[source] "test_bit_power_oracles()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_bit_rotation_oracles()" as test_bit_rotation_oracles_spec
    from source with (\post emp).
  Lemma test_bit_rotation_oracles_ok : verify[source] "test_bit_rotation_oracles()".
  Proof. verify_spec; go $usenamed=true. Qed.

End with_cpp.

(** Closed negative/load-bearing evidence for the sole API precondition. *)
Lemma bit_ceil_unrepresentable_range_is_rejected x :
  (uint32_high_bit < x < uint32_modulus)%N ->
  bit_ceil_api x = None.
Proof.
  intros [Hhigh Hvalid].
  unfold bit_ceil_api.
  apply N.ltb_lt in Hvalid. rewrite Hvalid.
  apply N.leb_gt in Hhigh. rewrite Hhigh.
  reflexivity.
Qed.
