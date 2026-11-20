(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Export skylabs.brick.libstdcpp.test.pthread.mutex_init.init.pred.
Require Export skylabs.brick.libstdcpp.pthread.mutex_init.spec.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.bi.tls_modalities.
Require skylabs.brick.libstdcpp.test.pthread.mutex_init.init_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_init.init_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  Context `{!HasStdThreads Σ, !HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.

  cpp.spec "init_default_mutex"
    from source
    as init_default_mutex_spec
    with (\arg{p : ptr} "mutex" (Vptr p)
          \with (P : mpred)
          \require LocalWith procTI P
          \prepost{tid} current_thread tid
          \pre (mutex_available p ∨ (p |-> uninitR "pthread_mutex_t" 1$m))%I ** P
          \post{status : Z}[Vint status]
            if bool_decide (status = 0%Z) then
              ∃ g, mutex_live p g P ** mutex_access g 1%Qp
            else mutex_init_failure p P status).
End with_cpp.
