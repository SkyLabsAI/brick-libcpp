(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.bi.linearity.
Require Export skylabs.brick.libstdcpp.test.pthread.equal.compare.pred.
Require Export skylabs.brick.libstdcpp.pthread.equal.spec.
Require skylabs.brick.libstdcpp.test.pthread.equal.compare_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.equal.compare_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ}.

  cpp.spec "compare_same(unsigned long)"
    as compare_same_spec
    with (\arg{id : thread_idT} "id" (Vthread id)
          \prepost{r q g} pthread_equal_pred.operands r id id q q g g
          \post[Vbool true] emp).

  cpp.spec "compare_distinct(unsigned long, unsigned long)"
    as compare_distinct_spec
    with (\arg{a : thread_idT} "first" (Vthread a)
          \arg{b : thread_idT} "second" (Vthread b)
          \pre [| a <> b |]
          \prepost{r qa qb ga gb} pthread_equal_pred.operands r a b qa qb ga gb
          \post[Vbool true] emp).
End with_cpp.
