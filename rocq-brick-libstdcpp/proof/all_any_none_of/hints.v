(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.all_any_none_of.pred.

NES.Begin all_any_none_of.

Lemma all_value_function (f : Z -> bool) xs :
  all_value (fun x => Some (f x)) xs = Some (forallb f xs).
Proof.
  unfold all_value.
  induction xs as [|x xs IH]; simpl; first reflexivity.
  destruct (f x); simpl in *.
  - exact IH.
  - reflexivity.
Qed.

Lemma any_value_function (f : Z -> bool) xs :
  any_value (fun x => Some (f x)) xs = Some (existsb f xs).
Proof.
  unfold any_value.
  induction xs as [|x xs IH]; simpl; first reflexivity.
  destruct (f x); simpl in *.
  - reflexivity.
  - exact IH.
Qed.

Lemma none_value_function (f : Z -> bool) xs :
  none_value (fun x => Some (f x)) xs = Some (negb (existsb f xs)).
Proof. rewrite /none_value any_value_function. reflexivity. Qed.

NES.End all_any_none_of.
Import all_any_none_of.
