(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From Stdlib Require Import ZArith.
Require Export skylabs.brick.libstdcpp.pthread.mutex.model.

(* Ubuntu Noble amd64 glibc 2.39-0ubuntu8.12 <errno.h>. The pinned C
   compilation and GNU C++17 client translations independently observe 16. *)
Definition pthread_mutex_trylock_ebusy : Z := 16%Z.
