(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.numbers.
Require Import skylabs.prelude.bytestring.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Definition byte_ord (c : Byte.byte) : Z :=
  Z.of_N (Byte.to_N c).

Fixpoint strlen (s : bs) : N :=
  match s with
  | BS.EmptyString => 0%N
  | BS.String _ rest => (1 + strlen rest)%N
  end.

Fixpoint strlen_bytes (bytes : list N) : N :=
  match bytes with
  | nil => 0%N
  | cons c rest =>
      if bool_decide (c = 0%N) then 0%N
      else (1 + strlen_bytes rest)%N
  end.

Fixpoint strcmp (s1 s2 : bs) : Z :=
  match s1, s2 with
  | BS.EmptyString, BS.EmptyString => 0
  | BS.EmptyString, BS.String c2 _ => - byte_ord c2
  | BS.String c1 _, BS.EmptyString => byte_ord c1
  | BS.String c1 rest1, BS.String c2 rest2 =>
      if bool_decide (c1 = c2) then strcmp rest1 rest2
      else byte_ord c1 - byte_ord c2
  end.

Fixpoint strncmp_nat (n : nat) (s1 s2 : bs) : Z :=
  match n with
  | O => 0
  | S n' =>
      match s1, s2 with
      | BS.EmptyString, BS.EmptyString => 0
      | BS.EmptyString, BS.String c2 _ => - byte_ord c2
      | BS.String c1 _, BS.EmptyString => byte_ord c1
      | BS.String c1 rest1, BS.String c2 rest2 =>
          if bool_decide (c1 = c2) then strncmp_nat n' rest1 rest2
          else byte_ord c1 - byte_ord c2
      end
  end.

Definition strncmp (s1 s2 : bs) (n : N) : Z :=
  strncmp_nat (N.to_nat n) s1 s2.

#[local] Open Scope bs_scope.

Succeed Example strlen_empty : strlen "" = 0%N := eq_refl.
Succeed Example strlen_three : strlen "abc" = 3%N := eq_refl.

Succeed Example strlen_bytes_empty : strlen_bytes nil = 0%N := eq_refl.
Succeed Example strlen_bytes_three :
  strlen_bytes (97%N :: 98%N :: 99%N :: nil) = 3%N := eq_refl.
Succeed Example strlen_bytes_embedded_null :
  strlen_bytes (97%N :: 98%N :: 0%N :: 99%N :: 100%N :: nil) = 2%N :=
  eq_refl.

Succeed Example strcmp_equal : strcmp "abc" "abc" = 0 := eq_refl.
Succeed Example strcmp_less : strcmp "abc" "abd" = -1 := eq_refl.
Succeed Example strcmp_greater : strcmp "abd" "abc" = 1 := eq_refl.
Succeed Example strcmp_prefix_less : strcmp "ab" "abc" = -99 := eq_refl.
Succeed Example strcmp_prefix_greater : strcmp "abc" "ab" = 99 := eq_refl.

Succeed Example strncmp_zero : strncmp "abc" "abd" 0 = 0 := eq_refl.
Succeed Example strncmp_equal_prefix : strncmp "abc" "abd" 2 = 0 := eq_refl.
Succeed Example strncmp_diff_at_bound : strncmp "abc" "abd" 3 = -1 := eq_refl.
