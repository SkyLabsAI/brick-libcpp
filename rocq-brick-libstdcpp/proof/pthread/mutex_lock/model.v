(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.mutex.model.
From Stdlib Require Import ZArith.

(* EDEADLK from the selected Ubuntu Noble amd64 glibc headers. *)
Definition mutex_lock_deadlock_code : Z := 35%Z.
