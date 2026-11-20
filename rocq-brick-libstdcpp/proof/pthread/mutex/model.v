(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.auto.cpp.proof.

Inductive mutex_state :=
| MutexUnlocked
| MutexLocked (owner : thread_idT) (loan : Qp).

Canonical Structure mutex_stateO := leibnizO mutex_state.
#[global] Instance mutex_state_inhabited : Inhabited mutex_state := populate MutexUnlocked.

Record mutex_generation := {
  mutex_state_name : iprop.gname;
  mutex_lifetime_name : iprop.gname;
}.

Definition mutex_namespace (g : mutex_generation) : namespace :=
  nroot .@@ "pthread" .@@ "default_mutex" .@ g.(mutex_state_name).
