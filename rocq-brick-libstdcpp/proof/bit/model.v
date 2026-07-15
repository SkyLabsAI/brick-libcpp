(*
 * Pure C++20 <bit> model for the concrete std::uint32_t specialization.
 * Values are N below 2^32, count results are Z, and rotation counts are Z
 * values already constrained by the public C++ int parameter type.
 *)
From Stdlib Require Import NArith ZArith Bool.

Definition uint32_width : N := 32%N.
Definition uint32_modulus : N := (2 ^ uint32_width)%N.
Definition uint32_max : N := (uint32_modulus - 1)%N.
Definition uint32_high_bit : N := (2 ^ 31)%N.
Definition int32_min : Z := (-2147483648)%Z.
Definition int32_max : Z := 2147483647%Z.

Definition valid_uint32 (x : N) : Prop := (x < uint32_modulus)%N.
Definition valid_int32 (s : Z) : Prop :=
  (int32_min <= s <= int32_max)%Z.
Definition valid_int32b (s : Z) : bool :=
  Z.leb int32_min s && Z.leb s int32_max.

Fixpoint popcount_loop (fuel : nat) (x : N) : nat :=
  match fuel with
  | O => O
  | S index =>
      popcount_loop index x +
        if N.testbit x (N.of_nat index) then 1 else 0
  end.

Fixpoint countl_zero_loop (fuel : nat) (x : N) : nat :=
  match fuel with
  | O => O
  | S index =>
      if N.testbit x (N.of_nat index)
      then O
      else S (countl_zero_loop index x)
  end.

Fixpoint countl_one_loop (fuel : nat) (x : N) : nat :=
  match fuel with
  | O => O
  | S index =>
      if N.testbit x (N.of_nat index)
      then S (countl_one_loop index x)
      else O
  end.

Fixpoint countr_zero_loop (index fuel : nat) (x : N) : nat :=
  match fuel with
  | O => O
  | S remaining =>
      if N.testbit x (N.of_nat index)
      then O
      else S (countr_zero_loop (S index) remaining x)
  end.

Fixpoint countr_one_loop (index fuel : nat) (x : N) : nat :=
  match fuel with
  | O => O
  | S remaining =>
      if N.testbit x (N.of_nat index)
      then S (countr_one_loop (S index) remaining x)
      else O
  end.

Definition popcount (x : N) : Z :=
  Z.of_nat (popcount_loop 32 x).

Definition countl_zero (x : N) : Z :=
  Z.of_nat (countl_zero_loop 32 x).

Definition countl_one (x : N) : Z :=
  Z.of_nat (countl_one_loop 32 x).

Definition countr_zero (x : N) : Z :=
  Z.of_nat (countr_zero_loop 0 32 x).

Definition countr_one (x : N) : Z :=
  Z.of_nat (countr_one_loop 0 32 x).

Definition has_single_bit (x : N) : bool :=
  Z.eqb (popcount x) 1.

Definition bit_width (x : N) : Z :=
  Z.of_N (N.size x).

Definition bit_floor (x : N) : N :=
  if N.eqb x 0 then 0%N else (2 ^ N.pred (N.size x))%N.

Definition bit_ceil (x : N) : N :=
  if N.leb x 1 then 1%N else (2 ^ N.size (x - 1))%N.

Definition rotation_amount (s : Z) : N :=
  Z.to_N (Z.modulo s 32).

Definition rotl (x : N) (s : Z) : N :=
  let r := rotation_amount s in
  N.land
    (N.lor (N.shiftl x r) (N.shiftr x (uint32_width - r)))
    uint32_max.

Definition rotr (x : N) (s : Z) : N :=
  let r := rotation_amount s in
  N.land
    (N.lor (N.shiftr x r) (N.shiftl x (uint32_width - r)))
    uint32_max.

Definition popcount_api (x : N) : option Z :=
  if N.ltb x uint32_modulus then Some (popcount x) else None.
Definition countl_zero_api (x : N) : option Z :=
  if N.ltb x uint32_modulus then Some (countl_zero x) else None.
Definition countr_zero_api (x : N) : option Z :=
  if N.ltb x uint32_modulus then Some (countr_zero x) else None.
Definition countl_one_api (x : N) : option Z :=
  if N.ltb x uint32_modulus then Some (countl_one x) else None.
Definition countr_one_api (x : N) : option Z :=
  if N.ltb x uint32_modulus then Some (countr_one x) else None.
Definition bit_width_api (x : N) : option Z :=
  if N.ltb x uint32_modulus then Some (bit_width x) else None.
Definition bit_floor_api (x : N) : option N :=
  if N.ltb x uint32_modulus then Some (bit_floor x) else None.
Definition has_single_bit_api (x : N) : option bool :=
  if N.ltb x uint32_modulus then Some (has_single_bit x) else None.

Definition bit_ceil_api (x : N) : option N :=
  if N.ltb x uint32_modulus then
    if N.leb x uint32_high_bit then Some (bit_ceil x) else None
  else None.

Definition rotl_api (x : N) (s : Z) : option N :=
  if N.ltb x uint32_modulus then
    if valid_int32b s then Some (rotl x s) else None
  else None.

Definition rotr_api (x : N) (s : Z) : option N :=
  if N.ltb x uint32_modulus then
    if valid_int32b s then Some (rotr x s) else None
  else None.

(** The standard-defined domain boundary is load-bearing. *)
Example bit_ceil_high_bit_is_defined :
  bit_ceil_api uint32_high_bit = Some uint32_high_bit.
Proof. vm_compute. reflexivity. Qed.

Example bit_ceil_above_high_bit_is_unavailable :
  bit_ceil_api (uint32_high_bit + 1) = None.
Proof. vm_compute. reflexivity. Qed.
