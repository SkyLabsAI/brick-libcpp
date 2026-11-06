(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cerrno.spec.
Require Import skylabs.brick.libstdcpp.test.cerrno.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ} `{!HasStdThreads Σ}.

  (* ERANGE is 34 on Linux. *)
  cpp.spec "test_errno_roundtrip()" with
    (\persist{th} current_thread th
     \pre{v} errnoR th 1$m v
     \post errnoR th 1$m 34).
  Lemma test_errno_roundtrip_ok : verify[source] "test_errno_roundtrip()".
  Proof. verify_spec; go. Qed.

  (* No ownership needed: only the address is compared. *)
  cpp.spec "test_errno_same_object()" default.
  Lemma test_errno_same_object_ok : verify[source] "test_errno_same_object()".
  Proof using HasStdThreads0 MOD. verify_spec; go. Qed.
End with_cpp.
