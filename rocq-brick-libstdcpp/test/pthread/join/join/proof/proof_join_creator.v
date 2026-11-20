(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.bi.linearity.
Require Import skylabs.brick.libstdcpp.test.pthread.join.join.spec.
Require Import skylabs.brick.libstdcpp.pthread.join.spec.
Require skylabs.brick.libstdcpp.test.pthread.join.join_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.join.join_cpp.source.

#[local] Hint Opaque lifecycle_join.slot_before lifecycle_join.slot_after
  lifecycle.id_valid lifecycle.joined pthread_create.completion_right
  pthread_create.registry_sync : sl_opacity.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry,
    !pthread_join.ProcessWaitDiscipline}.
  Set Default Proof Using "MOD".

  #[local] Existing Instance pthread_join.join_spec_spec_instance.

  Lemma join_creator_ok :
    verify[source] "join_creator".
  Proof.
    verify_spec.
    go.
    iExists slot, g, Post, old. go.
    rename _x_ into result.
    iExists result. go.

  Qed.
End with_cpp.
