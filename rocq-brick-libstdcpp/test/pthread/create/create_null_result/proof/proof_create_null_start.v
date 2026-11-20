(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.pthread.create.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.create.create_null_result.spec.
Require skylabs.brick.libstdcpp.test.pthread.create.create_null_result_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.create.create_null_result_cpp.source.

#[local] Hint Opaque lifecycle.running : sl_opacity.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ}.
  Set Default Proof Using "MOD".

  Lemma create_null_start_ok :
    verify[source] "create_null_start".
  Proof.
    verify_spec.
    rewrite /null_pre.
    go.
    rewrite /null_post.
    go.
  Qed.
End with_cpp.
