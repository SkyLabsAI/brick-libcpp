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

  Lemma compare_same_ok :
    verify[source] "compare_same(unsigned long)".
  Proof.
    verify_spec; go.
    iExists r, q, q, g, g.
    go.
    iPureIntro. eapply pthread_equal_model.result_same. eassumption.
  Qed.
End with_cpp.
