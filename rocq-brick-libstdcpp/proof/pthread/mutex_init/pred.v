(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.mutex_init.model.
Require Export skylabs.brick.libstdcpp.pthread.mutex.pred.
Require Import skylabs.auto.cpp.prelude.pred.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (* Failure returns P and typed ownership with unspecified contents. The
     common protocol's fresh ingress requires uninitR; this gives only anyR. *)
  Definition mutex_init_failure (p : ptr) (P : mpred) (status : Z) : mpred :=
    [| mutex_init_error status |] ** (p |-> anyR "pthread_mutex_t" 1$m) ** P.
End with_cpp.

#[global] Hint Opaque mutex_init_failure : sl_opacity.
