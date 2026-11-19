(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Export skylabs.brick.libstdcpp.pthread.self.spec.
Require skylabs.brick.libstdcpp.test.pthread.self.identity_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.self.identity_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  Context `{!HasStdThreads Σ}.

  cpp.spec "observe_pthread_self"
    as observe_pthread_self_spec
    with (\prepost{tid} current_thread tid
          \post[Vthread tid] emp).
End with_cpp.
