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

  Parameter later_than : abs_time -> mpred.
  Parameter later_than_knowledge : Knowledge1 later_than.
  Parameter later_than_timeless : Timeless1 later_than.
  Parameter later_than_weakly_objective : WeaklyObjective1 later_than.
  Axiom later_than_down_closed :
    forall t1 t2,
      (t1 <= t2)%N ->
      later_than (abs_time_of_N t2) |-- later_than (abs_time_of_N t1).

  #[global] Existing Instance later_than_knowledge.
  #[global] Existing Instance later_than_timeless.
  #[global] Existing Instance later_than_weakly_objective.

  (** Abstract model for the non-standard tail of glibc's [struct tm].

      The public [tm_model] and [tmR] expose only the 9 ISO C fields.
      Anything specific to the extra glibc fields lives here instead.

      For now we choose the smallest possible hidden model, namely [unit]:
      clients learn nothing about [tm_gmtoff] or [tm_zone], and the hidden
      tail is represented only through [tmR_hidden]. This keeps the current
      TODO local: we can later replace [unit] with a richer model once we
      decide whether [tm_zone] should be owned, borrowed, or abstracted in
      some other way. *)
  Definition hidden_tm_bits : Type := unit.

  (** Representation of the hidden, non-standard tail of [struct tm].

      This predicate is the only place where the glibc-specific fields
      [tm_gmtoff] and [tm_zone] may appear. It is meant to describe those
      fields relative to the enclosing [tm] object while keeping their exact
      ownership story abstract from clients of [tmR].

      The hidden index is currently [unit], so [tmR_hidden] is effectively a
      single abstract tail predicate. If we later decide to expose some hidden
      semantic information, this is the place to refine. *)
  Parameter tmR_hidden :
    cQp.t -> hidden_tm_bits -> Rep.
  #[only(cfracsplittable)] derive tmR_hidden.

  Parameter timespecR_raw : cQp.t -> timespec_model -> Rep.
  #[only(type_ptr="timespec", cfracsplittable)] derive timespecR_raw.
End with_cpp.

sl.lock
Definition tmR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (tm : tm_model) : Rep :=
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
  tmR_hidden q tt.
#[only(lazy_unfold)] derive tmR.
#[only(type_ptr,cfracsplittable)] derive tmR.

sl.lock
Definition timespecR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (ts : timespec_model) : Rep :=
  timespecR_raw q ts.
#[only(lazy_unfold)] derive timespecR.
#[only(type_ptr,cfracsplittable)] derive timespecR.

#[global] Instance tmR_learnable `{Σ : cpp_logic} {σ : genv} : LearnEqF1 tmR :=
  ltac:(solve_learnable).

#[global] Instance timespecR_learnable `{Σ : cpp_logic} {σ : genv} : LearnEqF1 timespecR :=
  ltac:(solve_learnable).
