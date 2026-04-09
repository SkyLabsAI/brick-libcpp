(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.

Require Export skylabs.brick.libstdcpp.ctime.pred.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Definition TIME_UTC : Z := 1.

Definition clock_t_model := Z.
Definition time_t_model := Z.

Parameter clock_result : clock_t_model -> Prop.
Parameter current_time_result : time_t_model -> Prop.
Parameter timespec_get_result : timespec_model -> Prop.
Parameter utc_time_to_tm : time_t_model -> tm_model -> Prop.
Parameter local_time_to_tm : time_t_model -> tm_model -> Prop.
Parameter mktime_result : tm_model -> tm_model -> time_t_model -> Prop.
Parameter asctime_text_of : tm_model -> cstring.t -> Prop.
Parameter strftime_text_of : cstring.t -> tm_model -> cstring.t -> Prop.

Definition ctime_text_of (t : time_t_model) (out : cstring.t) : Prop :=
  exists tm, local_time_to_tm t tm /\ asctime_text_of tm out.

Axiom timespec_get_result_wf :
  forall ts,
    timespec_get_result ts ->
    0 <= timespec_model_nsec ts < 1000000000.

Axiom asctime_text_of_len :
  forall tm out,
    asctime_text_of tm out ->
    cstring.size out = 25.

Axiom strftime_text_of_fit :
  forall fmt tm out bound,
    strftime_text_of fmt tm out ->
    bound = cstring.size out ->
    0 <= bound.
