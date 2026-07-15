(* Exact black-box C++20 <bit> specs for unsigned int (std::uint32_t here). *)
Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.bit.pred.
Require Import skylabs.brick.libstdcpp.bit.inc_bit_cpp.

#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "std::popcount<unsigned int>(unsigned int)" as popcount_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (popcount (Z.to_N x))] emp).

  cpp.spec "std::countl_zero<unsigned int>(unsigned int)" as countl_zero_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (countl_zero (Z.to_N x))] emp).

  cpp.spec "std::countr_zero<unsigned int>(unsigned int)" as countr_zero_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (countr_zero (Z.to_N x))] emp).

  cpp.spec "std::countl_one<unsigned int>(unsigned int)" as countl_one_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (countl_one (Z.to_N x))] emp).

  cpp.spec "std::countr_one<unsigned int>(unsigned int)" as countr_one_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (countr_one (Z.to_N x))] emp).

  (* libstdc++ 12 spells this pre-LWG-3656 specialization as unsigned int;
     the mathematical result is still the exact Z-valued bit width. *)
  cpp.spec "std::bit_width<unsigned int>(unsigned int)" as bit_width_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (bit_width (Z.to_N x))] emp).

  cpp.spec "std::bit_ceil<unsigned int>(unsigned int)" as bit_ceil_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \require (0 <= x <= Z.of_N uint32_high_bit)
      \post[Vint (Z.of_N (bit_ceil (Z.to_N x)))] emp).

  cpp.spec "std::bit_floor<unsigned int>(unsigned int)" as bit_floor_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vint (Z.of_N (bit_floor (Z.to_N x)))] emp).

  cpp.spec "std::has_single_bit<unsigned int>(unsigned int)" as has_single_bit_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \post[Vbool (has_single_bit (Z.to_N x))] emp).

  cpp.spec "std::rotl<unsigned int>(unsigned int, int)" as rotl_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \arg{s} "__s" (Vint s)
      \post[Vint (Z.of_N (rotl (Z.to_N x) s))] emp).

  cpp.spec "std::rotr<unsigned int>(unsigned int, int)" as rotr_spec
    from inc_bit_cpp.source with (
      \arg{x} "__x" (Vint x)
      \arg{s} "__s" (Vint s)
      \post[Vint (Z.of_N (rotr (Z.to_N x) s))] emp).

End with_cpp.
