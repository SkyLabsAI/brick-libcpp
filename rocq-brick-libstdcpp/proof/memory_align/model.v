From Stdlib Require Import Bool PeanoNat ZArith.

#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.

(** Pure, client-visible outcome of [std::align].  The outer option excludes
    calls outside the standard-defined numeric domain. *)
Definition align_outcome := (option Z * (Z * Z))%type.

(** Executable recognition of the positive powers of two. *)
Definition is_power_of_two (alignment : Z) : bool :=
  (0 <? alignment) &&
  Nat.eqb (Z.to_nat alignment)
    (Nat.pow 2 (Nat.log2 (Z.to_nat alignment))).

(** Propositional form used at the [cpp.spec] UB boundary. *)
Definition mathematical_power_of_two (alignment : Z) : Prop :=
  exists exponent : nat,
    alignment = Z.of_nat (Nat.pow 2 exponent).

Definition align_domain
    (alignment size ptr space : Z) : bool :=
  is_power_of_two alignment &&
  (0 <=? size) && (0 <=? ptr) && (0 <=? space).

(** Least nonnegative byte offset that reaches an alignment multiple. *)
Definition alignment_skip (alignment ptr : Z) : Z :=
  (- ptr) mod alignment.

Definition first_aligned_address (alignment ptr : Z) : Z :=
  ptr + alignment_skip alignment ptr.

Definition aligned_block_fits
    (alignment size ptr space : Z) : bool :=
  alignment_skip alignment ptr + size <=? space.

(** Public behavioral adapter required by the frozen strength laws. *)
Definition align_call
    (alignment size ptr space : Z) : option align_outcome :=
  if align_domain alignment size ptr space then
    let skip := alignment_skip alignment ptr in
    let aligned := ptr + skip in
    if skip + size <=? space then
      Some (Some aligned, (aligned, space - skip))
    else
      Some (None, (ptr, space))
  else
    None.

(** Exact standard transition, used by the public-contract obligation proof. *)
Definition align_transition
    (alignment size ptr space : Z)
    (result : option Z) (ptr_after space_after : Z) : Prop :=
  let skip := alignment_skip alignment ptr in
  let aligned := ptr + skip in
  if skip + size <=? space then
    result = Some aligned /\
    ptr_after = aligned /\
    space_after = space - skip
  else
    result = None /\
    ptr_after = ptr /\
    space_after = space.

(** N-valued projection used directly by the C++ size_t/pointer spec. *)
Definition alignment_skipN (alignment ptr : N) : N :=
  Z.to_N (alignment_skip (Z.of_N alignment) (Z.of_N ptr)).

Definition aligned_block_fitsN
    (alignment size ptr space : N) : bool :=
  (alignment_skipN alignment ptr + size <=? space)%N.

Definition first_aligned_addressN (alignment ptr : N) : N :=
  (ptr + alignment_skipN alignment ptr)%N.

Definition space_afterN
    (alignment size ptr space : N) : N :=
  if aligned_block_fitsN alignment size ptr space then
    (space - alignment_skipN alignment ptr)%N
  else space.

