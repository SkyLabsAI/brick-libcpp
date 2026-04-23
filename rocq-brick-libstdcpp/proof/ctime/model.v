(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.cpp.string.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Record tm_t := {
  tm_model_sec : Z;
  tm_model_min : Z;
  tm_model_hour : Z;
  tm_model_mday : Z;
  tm_model_mon : Z;
  tm_model_year : Z;
  tm_model_wday : Z;
  tm_model_yday : Z;
  tm_model_isdst : Z;
}.

Record timespec_t := {
  timespec_model_sec : Z;
  timespec_model_nsec : Z;
}.

Definition TIME_UTC : Z := 1.

Definition clock_t := Z.
Definition time_t := Z.

Parameter abs_time_t : Type.
Parameter abs_time_of_N : N -> abs_time_t.
Parameter abs_time_diff_t : Type.

Definition timespec_wf (ts : timespec_t) : Prop :=
  0 <= timespec_model_nsec ts < 1000000000.

Parameter time_t_to_abs_time : time_t -> abs_time_t -> Prop.
Parameter timespec_to_abs_time : timespec_t -> abs_time_t -> Prop.
Parameter clock_t_to_abs_time_diff : clock_t -> abs_time_diff_t -> Prop.
Parameter abs_time_plus_diff : abs_time_t -> abs_time_diff_t -> abs_time_t -> Prop.

Parameter utc_time_to_tm : time_t -> tm_t -> Prop.
Parameter local_time_to_tm : time_t -> tm_t -> Prop.
Parameter mktime_result : tm_t -> tm_t -> time_t -> Prop.
Parameter asctime_text_of : tm_t -> cstring.t -> Prop.
Parameter strftime_text_of : cstring.t -> tm_t -> cstring.t -> Prop.

Definition ctime_text_of (t : time_t) (out : cstring.t) : Prop :=
  exists tm, local_time_to_tm t tm /\ asctime_text_of tm out.

Axiom asctime_text_of_len :
  forall tm out,
    asctime_text_of tm out ->
    cstring.size out = 25.

Axiom strftime_text_of_fit :
  forall fmt tm out bound,
    strftime_text_of fmt tm out ->
    bound = cstring.size out ->
    0 <= bound.
