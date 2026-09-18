(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.list_numbers.
Require Import elpi.apps.NES.NES.

#[local] Open Scope Z_scope.

NES.Begin all_any_none_of.

(* [None] permits either predicate result. *)
Definition all_value (test : Z -> option bool) (xs : list Z) : option bool :=
  if existsb (fun x => bool_decide (test x = Some false)) xs then Some false
  else if forallb (fun x => bool_decide (test x = Some true)) xs then Some true
  else None.

Definition any_value (test : Z -> option bool) (xs : list Z) : option bool :=
  if existsb (fun x => bool_decide (test x = Some true)) xs then Some true
  else if forallb (fun x => bool_decide (test x = Some false)) xs then Some false
  else None.

Definition none_value (test : Z -> option bool) (xs : list Z) : option bool :=
  negb <$> any_value test xs.

Succeed Example empty_all : all_value (fun _ => None) [] = Some true := eq_refl.
Succeed Example empty_any : any_value (fun _ => None) [] = Some false := eq_refl.
Succeed Example empty_none : none_value (fun _ => None) [] = Some true := eq_refl.
Succeed Example high_bytes_all :
  all_value (fun x => Some (bool_decide (128 <= x))) [128; 255] = Some true := eq_refl.
Succeed Example mixed_all :
  all_value (fun x => Some (bool_decide (x <> 0))) [128; 0; 255] = Some false := eq_refl.
Succeed Example mixed_any :
  any_value (fun x => Some (bool_decide (x <> 0))) [128; 0; 255] = Some true := eq_refl.
Succeed Example zero_none :
  none_value (fun x => Some (bool_decide (x <> 0))) [0; 0] = Some true := eq_refl.
Succeed Example singleton_all :
  all_value (fun x => Some (bool_decide (x <> 0))) [0] = Some false := eq_refl.
Succeed Example singleton_any :
  any_value (fun x => Some (bool_decide (x <> 0))) [7] = Some true := eq_refl.
Succeed Example singleton_none :
  none_value (fun x => Some (bool_decide (x <> 0))) [7] = Some false := eq_refl.
Succeed Example low_bytes_any :
  any_value (fun x => Some (bool_decide (128 <= x))) [0; 127] = Some false := eq_refl.
Succeed Example unknown_all : all_value (fun _ => None) [0] = None := eq_refl.
Succeed Example unknown_any : any_value (fun _ => None) [0] = None := eq_refl.
Succeed Example partial_all :
  all_value (fun x => if bool_decide (x = 0) then Some false else None) [7; 0] = Some false := eq_refl.
Succeed Example partial_any :
  any_value (fun x => if bool_decide (x = 0) then None else Some true) [0; 7] = Some true := eq_refl.

NES.End all_any_none_of.
