(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer.spec.
Require skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex.static_initializer_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Set Default Proof Using "MOD".

  Lemma static_mutex_address_ok :
    verify[source] "static_mutex_address".
  Proof. verify_spec; go. Qed.
End with_cpp.
