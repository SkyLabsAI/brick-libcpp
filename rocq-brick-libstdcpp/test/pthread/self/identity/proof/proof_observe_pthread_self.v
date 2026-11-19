(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.self.identity.spec.
Require skylabs.brick.libstdcpp.test.pthread.self.identity_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.self.identity_cpp.source.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{HAS_THREADS : !HasStdThreads Σ}.
  Set Default Proof Using "MOD HAS_THREADS".

  Lemma observe_pthread_self_ok :
    verify[source] observe_pthread_self_spec.
  Proof. verify_spec; go. Qed.
End with_cpp.
