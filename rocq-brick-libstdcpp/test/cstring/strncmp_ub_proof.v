(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Import skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.test.cstring.strncmp_ub_cpp.

(** * The [strncmp] spec rejects reads past the end of a bounded buffer

    Each client in [strncmp_ub.cpp] gets stuck on [strncmp_readable "a" 2],
    which is false; see strncmp_ub_proof.expected. *)

(* As in proof.v: lets string literals be split into [cstring.R] fractions. *)
#[only(cfracsplittable)] derive cstring.R.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Goal strncmp_readable "a" 2 = false.
  Proof. done. Qed.

  cpp.spec "strncmp_overread_lhs()" from source default.
  Lemma strncmp_overread_lhs_ok : verify[source] "strncmp_overread_lhs()".
  Proof. verify_spec; go. Show. Fail Qed. Abort.

  cpp.spec "strncmp_overread_rhs()" from source default.
  Lemma strncmp_overread_rhs_ok : verify[source] "strncmp_overread_rhs()".
  Proof. verify_spec; go. Show. Fail Qed. Abort.
End with_cpp.
