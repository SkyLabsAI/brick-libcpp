(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.brick.libstdcpp.pthread.self.pred.
Require skylabs.brick.libstdcpp.pthread.inc_hpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ}.

  cpp.spec "pthread_self"
    from source
    as pthread_self_spec
    with (\prepost{tid} current_thread tid
          \post[Vthread tid] emp).
End with_cpp.
