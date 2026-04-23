(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.elpi.derive.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.iostream.pred.

Require Export skylabs.brick.libstdcpp.ctime.model.
Require Import skylabs.brick.libstdcpp.ctime.inc_ctime_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Parameter later_than : abs_time_t -> mpred.
  #[global] Declare Instance later_than_knowledge : Knowledge1 later_than.
  #[global] Declare Instance later_than_timeless : Timeless1 later_than.
  #[global] Declare Instance later_than_weakly_objective : WeaklyObjective1 later_than.
  Axiom later_than_down_closed :
    forall t1 t2,
      (t1 <= t2)%N ->
      later_than (abs_time_of_N t2) |-- later_than (abs_time_of_N t1).

  Parameter system_start_at : abs_time_t -> mpred.
  #[global] Declare Instance system_start_at_knowledge : Knowledge1 system_start_at.
  #[global] Declare Instance system_start_at_timeless : Timeless1 system_start_at.
  #[global] Declare Instance system_start_at_weakly_objective : WeaklyObjective1 system_start_at.

  (** Correctness of a [time] result, relative to the current-time world. *)
  Definition time_result (t : time_t) : mpred :=
    [| 0 <= t |] **
    Exists now,
      [| time_t_to_abs_time t now |] **
      later_than now.
  #[global] Hint Opaque time_result : typeclass_instances sl_opacity.
  #[global] Arguments time_result : simpl never.

  (** Correctness of a [timespec_get] result, relative to current absolute time. *)
  Definition timespec_get_result (ts : timespec_t) : mpred :=
    [| timespec_wf ts |] **
    Exists now,
      [| timespec_to_abs_time ts now |] **
      later_than now.
  #[global] Hint Opaque timespec_get_result : typeclass_instances sl_opacity.
  #[global] Arguments timespec_get_result : simpl never.

  (** Correctness of a [clock] result as duration since system start. *)
  Definition clock_result (ticks : clock_t) : mpred :=
    [| 0 <= ticks |] **
    Exists diff start now,
      [| clock_t_to_abs_time_diff ticks diff |] **
      system_start_at start **
      [| abs_time_plus_diff start diff now |] **
      later_than now.
  #[global] Hint Opaque clock_result : typeclass_instances sl_opacity.
  #[global] Arguments clock_result : simpl never.

  (** Representation of the hidden, non-standard tail of [struct tm].

      This predicate is the only place where the glibc-specific fields
      [tm_gmtoff] and [tm_zone] may appear. It is meant to describe those
      fields relative to the enclosing [tm] object while keeping their exact
      ownership story abstract from clients of [tmR].

      This predicate is intentionally unindexed: a provisional equation for a
      dummy hidden model would become part of the interface and make later
      refinements breaking changes. If clients eventually need semantic facts
      about the non-standard tail, introduce that model deliberately then.

      TODO: investigate whether [tm_zone] should be owned, borrowed, or
      abstracted away by this hidden representation. *)
  Parameter tmR_hidden : cQp.t -> Rep.
  #[only(cfracsplittable)] derive tmR_hidden.

  Parameter timespecR_raw : cQp.t -> timespec_t -> Rep.
  #[only(type_ptr="timespec", cfracsplittable)] derive timespecR_raw.
End with_cpp.

sl.lock
Definition tmR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (tm : tm_t) : Rep :=
  structR "tm" q **
  _field "tm::tm_sec" |-> primR Tint q (Vint tm.(tm_model_sec)) **
  _field "tm::tm_min" |-> primR Tint q (Vint tm.(tm_model_min)) **
  _field "tm::tm_hour" |-> primR Tint q (Vint tm.(tm_model_hour)) **
  _field "tm::tm_mday" |-> primR Tint q (Vint tm.(tm_model_mday)) **
  _field "tm::tm_mon" |-> primR Tint q (Vint tm.(tm_model_mon)) **
  _field "tm::tm_year" |-> primR Tint q (Vint tm.(tm_model_year)) **
  _field "tm::tm_wday" |-> primR Tint q (Vint tm.(tm_model_wday)) **
  _field "tm::tm_yday" |-> primR Tint q (Vint tm.(tm_model_yday)) **
  _field "tm::tm_isdst" |-> primR Tint q (Vint tm.(tm_model_isdst)) **
  tmR_hidden q.
#[only(lazy_unfold)] derive tmR.
#[only(type_ptr,cfracsplittable)] derive tmR.

sl.lock
Definition timespecR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (ts : timespec_t) : Rep :=
  timespecR_raw q ts.
#[only(lazy_unfold)] derive timespecR.
#[only(type_ptr,cfracsplittable)] derive timespecR.

#[global] Instance tmR_learnable `{Σ : cpp_logic} {σ : genv} : LearnEqF1 tmR :=
  ltac:(solve_learnable).

#[global] Instance timespecR_learnable `{Σ : cpp_logic} {σ : genv} : LearnEqF1 timespecR :=
  ltac:(solve_learnable).
