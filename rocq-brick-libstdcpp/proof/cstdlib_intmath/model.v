(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.numbers.

#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.

(** Implementation range used to make undefined behavior executable. *)
Definition value_range := (Z * Z)%type.

(** Test whether an integer is representable in an implementation range. *)
Definition representable (range : value_range) (z : Z) : bool :=
  let '(lo, hi) := range in
  (lo <=? z) && (z <=? hi).

(** Defined-domain adapter for an absolute-value contract. *)
Definition abs_adapter (range : value_range) (n : Z) : option Z :=
  if representable range n && representable range (Z.abs n)
  then Some (Z.abs n)
  else None.

(** Defined-domain adapter for a quotient/remainder contract. *)
Definition div_adapter
    (range : value_range) (numer denom : Z) : option (Z * Z)%type :=
  if representable range numer && representable range denom &&
     negb (denom =? 0) &&
     representable range (Z.quot numer denom) &&
     representable range (Z.rem numer denom)
  then Some (Z.quot numer denom, Z.rem numer denom)
  else None.

(** Exact mathematical result of the [int] absolute-value overload. *)
Definition abs_int (n : Z) : Z := Z.abs n.

(** Exact mathematical result of the [long] absolute-value overload. *)
Definition abs_long (n : Z) : Z := Z.abs n.

(** Exact mathematical result of the [long long] absolute-value overload. *)
Definition abs_long_long (n : Z) : Z := Z.abs n.

(** Exact mathematical result of [labs]. *)
Definition labs (n : Z) : Z := Z.abs n.

(** Exact mathematical result of [llabs]. *)
Definition llabs (n : Z) : Z := Z.abs n.

(** Quotient and remainder for [div(int, int)]. *)
Definition div_int (numer denom : Z) : Z * Z :=
  (Z.quot numer denom, Z.rem numer denom).

(** Quotient and remainder for [div(long, long)]. *)
Definition div_long (numer denom : Z) : Z * Z :=
  (Z.quot numer denom, Z.rem numer denom).

(** Quotient and remainder for [div(long long, long long)]. *)
Definition div_long_long (numer denom : Z) : Z * Z :=
  (Z.quot numer denom, Z.rem numer denom).

(** Quotient and remainder for [ldiv]. *)
Definition ldiv (numer denom : Z) : Z * Z :=
  (Z.quot numer denom, Z.rem numer denom).

(** Quotient and remainder for [lldiv]. *)
Definition lldiv (numer denom : Z) : Z * Z :=
  (Z.quot numer denom, Z.rem numer denom).
