(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.
Require Import Stdlib.Strings.String Stdlib.Strings.Byte.

(** * [std::istream >> int] on finite inputs

    [parse s] runs [istream.read_int] on the characters of [s], and returns
    its result and the characters left over. The examples match what
    libstdc++ does for [std::istringstream(s) >> n]
    ([facet.num.get.virtuals], [istream.formatted.arithmetic]). *)
Definition chars (s : String.string) : list N :=
  Byte.to_N <$> String.list_byte_of_string s.

Definition parse (s : String.string) :=
  istream.feed 4096 istream.read_int (chars s).

(** Values, with the delimiter that [read_int] reads ahead. *)
Example parse_plain : parse "12
x" = Some ((10%N, Some 12%Z), [120%N]) := eq_refl.
Example parse_ws_plus : parse "  +7 " = Some ((32%N, Some 7%Z), []) := eq_refl.
Example parse_neg_zero : parse "-0;" = Some ((59%N, Some 0%Z), []) := eq_refl.
Example parse_neg : parse "-35 " = Some ((32%N, Some (-35)%Z), []) := eq_refl.
Example parse_max : parse "2147483647 " = Some ((32%N, Some 2147483647%Z), []) := eq_refl.
Example parse_big : parse "2147483648 " = Some ((32%N, Some 2147483648%Z), []) := eq_refl.
Example parse_small : parse "-2147483649 " = Some ((32%N, Some (-2147483649)%Z), []) := eq_refl.
(** Conversion failures. *)
Example parse_letters : parse "abc" = Some ((97%N, None), [98; 99]%N) := eq_refl.
Example parse_sign_only : parse "-
" = Some ((10%N, None), []) := eq_refl.
Example parse_two_signs : parse "+-5" = Some ((45%N, None), [53%N]) := eq_refl.
(** Incomplete input: [read_int] waits for a character after the digits. *)
Example parse_eof : parse "12" = None := eq_refl.

(** What extraction stores, and whether it succeeds, for each result. *)
Example ok_plain : istream.int_ok (Some 12%Z) = true := eq_refl.
Example ok_max : istream.int_ok (Some 2147483647%Z) = true := eq_refl.
Example ok_min : istream.int_ok (Some (-2147483648)%Z) = true := eq_refl.
Example stored_plain : istream.int_stored (Some (-35)%Z) = (-35)%Z := eq_refl.
(** Out-of-range values store the nearest limit, and conversion failures 0;
    both fail. *)
Example ok_big : istream.int_ok (Some 2147483648%Z) = false := eq_refl.
Example stored_big : istream.int_stored (Some 2147483648%Z) = 2147483647%Z := eq_refl.
Example ok_small : istream.int_ok (Some (-2147483649)%Z) = false := eq_refl.
Example stored_small : istream.int_stored (Some (-2147483649)%Z) = (-2147483648)%Z := eq_refl.
Example ok_failure : istream.int_ok None = false := eq_refl.
Example stored_failure : istream.int_stored None = 0%Z := eq_refl.

(** The characters the stream holds are read first, and those left over stay. *)
Example run_buf_read_ahead :
  istream.feed 4096 (istream.run_buf [45%N] istream.read_int) (chars "34 ")
  = Some (((32%N, Some (-34)%Z), []), []) := eq_refl.
Example run_buf_left_over :
  istream.feed 4096 (istream.run_buf (chars "-34 56") istream.read_int) []
  = Some (((32%N, Some (-34)%Z), chars "56"), []) := eq_refl.
