(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.brick.libstdcpp.pthread.mutex_init.pred.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.bi.tls_modalities.
Require skylabs.brick.libstdcpp.pthread.inc_hpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ, !HasOwn (iPropI _Σ) (excl_authR mutex_stateO)}.

  (* The caller supplies exclusive available storage for the default normal,
     process-private, non-robust mutex. A successful call installs P in the
     common unlocked protocol. Static startup and byte-prefilled storage
     have no ingress in this contract. *)
  cpp.spec "pthread_mutex_init"
    from source
    as pthread_mutex_init_spec
    with (\arg{p : ptr} "__mutex" (Vptr p)
          \arg "__mutexattr" (Vptr nullptr)
          \with (P : mpred)
          \require LocalWith procTI P
          \prepost{tid} current_thread tid
          \pre mutex_available p ** P
          \post{status : Z}[Vint status]
            if bool_decide (status = 0%Z) then mutex_ready p P
            else mutex_init_failure p P status).
End with_cpp.
