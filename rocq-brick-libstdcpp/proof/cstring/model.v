(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.numbers.
Require Import skylabs.prelude.list_numbers.
Require Import skylabs.prelude.bytestring.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Definition byte_ord (c : Byte.byte) : Z :=
  Z.of_N (Byte.to_N c).

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

Definition byte_of_int (c : Z) : Z :=
  (c mod 256)%Z.

Fixpoint strchr (s : bs) (c : Z) : option Z :=
  match s with
  | BS.EmptyString =>
      if bool_decide (c = 0) then Some 0 else None
  | BS.String ch rest =>
      if bool_decide (c = byte_ord ch) then Some 0
      else option_map (fun off => (1 + off)%Z) (strchr rest c)
  end.

Fixpoint strrchr (s : bs) (c : Z) : option Z :=
  match s with
  | BS.EmptyString =>
      if bool_decide (c = 0) then Some 0 else None
  | BS.String ch rest =>
      match strrchr rest c with
      | Some off => Some (1 + off)%Z
      | None =>
          if bool_decide (c = byte_ord ch) then Some 0 else None
      end
  end.

Fixpoint contains (needle : Byte.byte) (haystack : bs) : bool :=
  match haystack with
  | BS.EmptyString => false
  | BS.String ch rest =>
      bool_decide (needle = ch) || contains needle rest
  end.

Fixpoint strspn (s accept : bs) : N :=
  match s with
  | BS.EmptyString => 0%N
  | BS.String ch rest =>
      if contains ch accept then N.succ (strspn rest accept) else 0%N
  end.

Fixpoint strcspn (s reject : bs) : N :=
  match s with
  | BS.EmptyString => 0%N
  | BS.String ch rest =>
      if contains ch reject then 0%N else N.succ (strcspn rest reject)
  end.

Fixpoint strpbrk (s accept : bs) : option Z :=
  match s with
  | BS.EmptyString => None
  | BS.String ch rest =>
      if contains ch accept then Some 0
      else option_map (fun off => (1 + off)%Z) (strpbrk rest accept)
  end.

Fixpoint prefix (needle haystack : bs) : bool :=
  match needle with
  | BS.EmptyString => true
  | BS.String n_ch n_rest =>
      match haystack with
      | BS.EmptyString => false
      | BS.String h_ch h_rest =>
          bool_decide (n_ch = h_ch) && prefix n_rest h_rest
      end
  end.

Fixpoint strstr (haystack needle : bs) : option Z :=
  match needle with
  | BS.EmptyString => Some 0
  | BS.String _ _ =>
      match haystack with
      | BS.EmptyString => None
      | BS.String _ rest =>
          if prefix needle haystack then Some 0
          else option_map (fun off => (1 + off)%Z) (strstr rest needle)
      end
  end.

Fixpoint memchr (bytes : list Z) (c : Z) : option Z :=
  match bytes with
  | nil => None
  | b :: rest =>
      if bool_decide (b = byte_of_int c) then Some 0
      else option_map (fun off => (1 + off)%Z) (memchr rest c)
  end.

Fixpoint memcmp (bytes1 bytes2 : list Z) : Z :=
  match bytes1, bytes2 with
  | nil, nil => 0
  | nil, b2 :: _ => - b2
  | b1 :: _, nil => b1
  | b1 :: rest1, b2 :: rest2 =>
      if bool_decide (b1 = b2) then memcmp rest1 rest2 else b1 - b2
  end.

Definition memset (c n : Z) : list Z :=
  replicateZ n (byte_of_int c).

Definition memcpy (bytes : list Z) : list Z :=
  bytes.

Definition memmove (bytes : list Z) : list Z :=
  bytes.

#[local] Open Scope bs_scope.

Succeed Example strcmp_equal : strcmp "abc" "abc" = 0 := eq_refl.
Succeed Example strcmp_less : strcmp "abc" "abd" = -1 := eq_refl.
Succeed Example strcmp_greater : strcmp "abd" "abc" = 1 := eq_refl.
Succeed Example strcmp_prefix_less : strcmp "ab" "abc" = -99 := eq_refl.
Succeed Example strcmp_prefix_greater : strcmp "abc" "ab" = 99 := eq_refl.

Succeed Example strncmp_zero : strncmp "abc" "abd" 0 = 0 := eq_refl.
Succeed Example strncmp_equal_prefix : strncmp "abc" "abd" 2 = 0 := eq_refl.
Succeed Example strncmp_diff_at_bound : strncmp "abc" "abd" 3 = -1 := eq_refl.

Succeed Example strchr_found : strchr "banana" 98 = Some 0 := eq_refl.
Succeed Example strchr_null : strchr "banana" 0 = Some 6 := eq_refl.
Succeed Example strchr_missing : strchr "banana" 122 = None := eq_refl.

Succeed Example strrchr_found : strrchr "banana" 97 = Some 5 := eq_refl.
Succeed Example strrchr_null : strrchr "banana" 0 = Some 6 := eq_refl.

Succeed Example strspn_prefix : strspn "abcde" "abc" = 3%N := eq_refl.
Succeed Example strcspn_prefix : strcspn "abcde" "dx" = 3%N := eq_refl.
Succeed Example strpbrk_found : strpbrk "abcdef" "xyc" = Some 2 := eq_refl.
Succeed Example strstr_found : strstr "abracadabra" "cad" = Some 4 := eq_refl.
Succeed Example strstr_empty : strstr "abracadabra" "" = Some 0 := eq_refl.

Succeed Example memchr_found : memchr [97; 0; 98]%Z 98 = Some 2 := eq_refl.
Succeed Example memchr_missing : memchr [97; 0; 98]%Z 122 = None := eq_refl.
Succeed Example memcmp_equal : memcmp [97; 0]%Z [97; 0]%Z = 0 := eq_refl.
Succeed Example memcmp_less : memcmp [97; 0; 120]%Z [97; 0; 121]%Z = -1 := eq_refl.
Succeed Example memset_wrap : memset 291 2 = [35; 35]%Z := eq_refl.
