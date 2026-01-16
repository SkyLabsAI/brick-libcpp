(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.Strings.Byte.
Require Import skylabs.prelude.numbers.

Require Import skylabs.prelude.bytestring.
Require Import skylabs.cpp.stdlib.cctype.spec.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

(** Helper function to convert a character to its digit value *)
Definition char_to_digit (c : Byte.byte) : option Z :=
  let z := Z.of_N (Byte.to_N c) in
  if isdigit (Byte.to_N c)
  then Some (z - Z.of_N (Byte.to_N "0"))%Z
  else None.

(** Helper function to parse the digits of a string into an integer *)
Fixpoint parse_digits (s : bs) (acc : Z) : Z :=
  match s with
  | BS.EmptyString => acc
  | BS.String c rest =>
      match char_to_digit c with
      | Some digit => parse_digits rest (acc * 10 + digit)
      | None => acc  (* Stop parsing at the first non-digit *)
      end
  end.

(** Skip leading whitespace in a string *)
Fixpoint skip_whitespace (s : bs) : bs :=
  match s with
  | BS.EmptyString => BS.EmptyString
  | BS.String c rest =>
      if isspace (Z.of_N (Byte.to_N c)) then skip_whitespace rest else BS.String c rest
  end.

(** Main atoi function that converts a string to an integer *)
Definition atoi (s : bs) : Z :=
  let s := skip_whitespace s in
  match s with
  | BS.EmptyString => 0
  | BS.String c rest =>
      match c with
      | "-"%byte => -1 * parse_digits rest 0
      | "+"%byte => parse_digits rest 0
      | _ =>
          match char_to_digit c with
          | Some digit => parse_digits rest digit
          | None => 0
          end
      end
  end.

(** Tests for char_to_digit function *)
Succeed Example char_to_digit_0 : char_to_digit "0" = Some 0 := eq_refl.
Succeed Example char_to_digit_1 : char_to_digit "1" = Some 1 := eq_refl.
Succeed Example char_to_digit_9 : char_to_digit "9" = Some 9 := eq_refl.
Succeed Example char_to_digit_invalid : char_to_digit "a" = None := eq_refl.
Succeed Example char_to_digit_space : char_to_digit " " = None := eq_refl.

#[local] Open Scope bs_scope.
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

(** More examples *)
Succeed Example test_atoi_1 : atoi "42" = 42 := eq_refl.
Succeed Example test_atoi_2 : atoi "-42" = -42 := eq_refl.
Succeed Example test_atoi_3 : atoi "  42" = 42 := eq_refl.
Succeed Example test_atoi_4 : atoi "+42" = 42 := eq_refl.
Succeed Example test_atoi_5 : atoi "42abc" = 42 := eq_refl.
Succeed Example test_atoi_6 : atoi "abc" = 0 := eq_refl.
Succeed Example test_atoi_7 : atoi "" = 0 := eq_refl.
