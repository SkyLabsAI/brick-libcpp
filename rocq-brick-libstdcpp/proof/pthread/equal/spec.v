(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.brick.libstdcpp.pthread.equal.pred.
Require skylabs.brick.libstdcpp.pthread.inc_hpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ}.

  cpp.spec "pthread_equal"
    from source
    as pthread_equal_spec
    with (\arg{a : thread_idT} "__thread1" (Vthread a)
          \arg{b : thread_idT} "__thread2" (Vthread b)
          \prepost{r qa qb ga gb} pthread_equal_pred.operands r a b qa qb ga gb
          \post{ret : Z}[Vint ret] [| pthread_equal_model.result a b ret |]).
End with_cpp.
