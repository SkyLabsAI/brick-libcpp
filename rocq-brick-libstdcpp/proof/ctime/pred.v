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

  (* TODO: Investigate whether [tm_zone] should be owned, borrowed, or abstracted away. *)
  Parameter tmR_hidden :
    cQp.t -> tm_model -> Rep.
  #[only(type_ptr="tm", cfracsplittable)] derive tmR_hidden.

  Parameter timespecR_raw : cQp.t -> timespec_model -> Rep.
  #[only(type_ptr="timespec", cfracsplittable)] derive timespecR_raw.
End with_cpp.

sl.lock
Definition tmR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (tm : tm_model) : Rep :=
  tmR_hidden q tm.
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
