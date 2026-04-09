(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.elpi.derive.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.iostream.pred.

Require Import skylabs.brick.libstdcpp.ctime.inc_ctime_cpp.

#[local] Set Primitive Projections.

Record tm_model := {
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

Record timespec_model := {
  timespec_model_sec : Z;
  timespec_model_nsec : Z;
}.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Parameter tmR_hidden :
    cQp.t -> tm_model -> Z -> cstring.t -> Rep.
  #[only(type_ptr="tm", cfracsplittable)] derive tmR_hidden.

  Definition tmR (q : cQp.t) (tm : tm_model) : Rep :=
    Exists gmtoff zone,
      tmR_hidden q tm gmtoff zone.

  Parameter timespecR : cQp.t -> timespec_model -> Rep.
  #[only(type_ptr="timespec", cfracsplittable)] derive timespecR.

  #[global] Instance timespecR_learnable : LearnEqF1 timespecR :=
    ltac:(solve_learnable).

End with_cpp.
