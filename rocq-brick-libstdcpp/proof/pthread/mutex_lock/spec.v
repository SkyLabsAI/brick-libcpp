(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.bi.tls_modalities.
Require Import iris.algebra.lib.excl_auth.
Require Export skylabs.brick.libstdcpp.pthread.mutex_lock.pred.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.
  Context `{!HasOwn (iPropI _Σ) (excl_authR mutex_stateO), !HasStdThreads Σ}.

  (* Partial correctness for a live normal, process-private, non-robust
     default mutex. A caller or waiter holds its access loan until the
     operation returns. Zero exchanges it for held ownership and P.
     Full access excludes another loan or a held token by the shared model's
     exclusion laws. For a fractional loan the contract conservatively admits
     POSIX's optional EDEADLK on detected deadlock and preserves the loan.
     The model exposes no wait-for graph or detection state. The shared
     handle and executing identity are preserved. *)
  cpp.spec "pthread_mutex_lock"
    from source
    as pthread_mutex_lock_spec
    with (\arg{p : ptr} "__mutex" (Vptr p)
          \prepost{(g : mutex_generation) (P : mpred) (owner : thread_idT)}
            mutex_live p g P ** current_thread owner
          \require (LocalWith procTI P)
          \pre{q : Qp} mutex_access g q
          \post{ret : Z}[Vint ret] mutex_lock_result g owner q P ret).
End with_cpp.
