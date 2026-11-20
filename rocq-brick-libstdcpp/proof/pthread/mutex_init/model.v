(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.mutex.model.
From Stdlib Require Import ZArith.

(* Error numbers for default attributes in the documented POSIX contract,
   encoded for the selected Ubuntu Noble amd64 headers. *)
Definition mutex_init_error (status : Z) : Prop :=
  (status = 11 \/ status = 12 \/ status = 1)%Z. (* EAGAIN, ENOMEM, EPERM *)
