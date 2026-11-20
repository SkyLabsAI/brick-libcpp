(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.mutex_lock.model.
Require Export skylabs.brick.libstdcpp.pthread.mutex.spec.
Require Import skylabs.auto.cpp.prelude.spec.
Require Import iris.algebra.lib.excl_auth.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.

  Definition mutex_lock_result (g : mutex_generation) (owner : thread_idT)
      (q : Qp) (P : mpred) (ret : Z) : mpred :=
    ([| ret = 0%Z |] ** mutex_held g owner q ** P) ∨
    ([| ret = mutex_lock_deadlock_code /\ q <> 1%Qp |] ** mutex_access g q).
End with_cpp.

#[global] Hint Opaque mutex_lock_result : sl_opacity.
