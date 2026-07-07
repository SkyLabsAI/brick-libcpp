(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.prelude.bytestring_core.
Require Import skylabs.brick.libstdcpp.cctype.spec.

Require Export skylabs.brick.libstdcpp.cstdlib.atoi_model.
Require Import skylabs.brick.libstdcpp.cstdlib.inc_cstdlib_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  #[local] Open Scope Z_scope.

  (* These functions require that their results are in-bounds to prevent UB. *)
  cpp.spec "atoi" with
    (\arg{buf} "str" (Vptr buf)
     \prepost{q str} buf |-> cstring.R q str
     \require valid<"int"> (atoi str)
     \post{n}[Vint n] emp).

  cpp.spec "atol" with
    (\arg{buf} "str" (Vptr buf)
     \prepost{q str} buf |-> cstring.R q str
     \require valid<"long"> (atoi str)
     \post{n}[Vint n] emp).

  cpp.spec "atoll" with
    (\arg{buf} "str" (Vptr buf)
     \prepost{q str} buf |-> cstring.R q str
     \require valid<"long long"> (atoi str)
     \post{n}[Vint n] emp).

End with_cpp.

#[local] Open Scope Z_scope.
(** Tests for char_to_digit function *)
Succeed Example char_to_digit_0 : char_to_digit "0" = Some 0 := eq_refl.
Succeed Example char_to_digit_1 : char_to_digit "1" = Some 1 := eq_refl.
Succeed Example char_to_digit_9 : char_to_digit "9" = Some 9 := eq_refl.
Succeed Example char_to_digit_invalid : char_to_digit "a" = None := eq_refl.
Succeed Example char_to_digit_space : char_to_digit " " = None := eq_refl.

(** Tests for skip_whitespace function *)
Succeed Example skip_whitespace_none : skip_whitespace "abc" = "abc" := eq_refl.
Succeed Example skip_whitespace_one : skip_whitespace " abc" = "abc" := eq_refl.
Succeed Example skip_whitespace_multiple : skip_whitespace "   abc" = "abc" := eq_refl.
Succeed Example skip_whitespace_mixed : skip_whitespace " 009 010abc" = "009 010abc" := eq_refl.
Succeed Example skip_whitespace_only : skip_whitespace "    " = "" := eq_refl.
Succeed Example skip_whitespace_empty : skip_whitespace "" = "" := eq_refl.

(** Tests for parse_digits function *)
Succeed Example parse_digits_empty : parse_digits "" 0 = 0 := eq_refl.
Succeed Example parse_digits_single : parse_digits "5" 0 = 5 := eq_refl.
Succeed Example parse_digits_multiple : parse_digits "123" 0 = 123 := eq_refl.
Succeed Example parse_digits_with_acc : parse_digits "45" 10 = 1045 := eq_refl.
Succeed Example parse_digits_stops_at_non_digit : parse_digits "123abc" 0 = 123 := eq_refl.
Succeed Example parse_digits_no_digits : parse_digits "abc" 0 = 0 := eq_refl.
Succeed Example parse_digits_starts_with_non_digit : parse_digits "a123" 0 = 0 := eq_refl.

(** Tests for atoi function - basic functionality *)
Succeed Example atoi_zero : atoi "0" = 0 := eq_refl.
Succeed Example atoi_positive : atoi "42" = 42 := eq_refl.
Succeed Example atoi_negative : atoi "-42" = -42 := eq_refl.
Succeed Example atoi_positive_sign : atoi "+42" = 42 := eq_refl.

(** Tests for atoi function - whitespace handling *)
Succeed Example atoi_leading_whitespace : atoi "  42" = 42 := eq_refl.
Succeed Example atoi_only_whitespace : atoi "   " = 0 := eq_refl.
Succeed Example atoi_whitespace_with_sign : atoi "  -42" = -42 := eq_refl.

(** Tests for atoi function - empty string *)
Succeed Example atoi_empty : atoi "" = 0 := eq_refl.

(** Tests for atoi function - non-digit characters *)
Succeed Example atoi_trailing_non_digit : atoi "42abc" = 42 := eq_refl.
Succeed Example atoi_only_non_digit : atoi "abc" = 0 := eq_refl.
Succeed Example atoi_leading_non_digit : atoi "abc42" = 0 := eq_refl.

(** Tests for atoi function - sign handling *)
Succeed Example atoi_only_plus_sign : atoi "+" = 0 := eq_refl.
Succeed Example atoi_only_minus_sign : atoi "-" = 0 := eq_refl.
Succeed Example atoi_plus_sign_with_non_digit : atoi "+abc" = 0 := eq_refl.
Succeed Example atoi_minus_sign_with_non_digit : atoi "-abc" = 0 := eq_refl.
Succeed Example atoi_double_signs : atoi "+-42" = 0 := eq_refl.
Succeed Example atoi_negative_zero : atoi "-0" = 0 := eq_refl.

(** Tests for atoi function - leading zeros *)
Succeed Example atoi_leading_zeros : atoi "007" = 7 := eq_refl.
Succeed Example atoi_negative_leading_zeros : atoi "-007" = -7 := eq_refl.

(** Tests for atoi function - complex cases *)
Succeed Example atoi_whitespace_sign_zeros_non_digits : atoi "  -0042abc" = -42 := eq_refl.
Succeed Example atoi_multiple_numbers : atoi "123 456" = 123 := eq_refl.
Succeed Example atoi_decimal_point : atoi "3.14" = 3 := eq_refl.
