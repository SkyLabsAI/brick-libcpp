(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.equal.compare.spec.
Require skylabs.brick.libstdcpp.test.pthread.equal.compare_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.equal.compare_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ}.
  Set Default Proof Using "MOD".

  Lemma compare_distinct_ok :
    verify[source] "compare_distinct(unsigned long, unsigned long)".
  Proof.
    verify_spec; go.
    iExists r, qa, qb, ga, gb.
    go.
    iPureIntro. eapply pthread_equal_model.result_distinct; eassumption.
  Qed.
End with_cpp.
