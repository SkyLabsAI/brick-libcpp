(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.

Require Import skylabs.brick.libstdcpp.test.vector.erase_ub_cpp.

(** * The vector [erase] spec rejects the past-the-end iterator

    [erase_end] gets stuck on [1 < 1]; see erase_ub_proof.expected. *)

(* As in test_cpp_proof.v. *)
#[local] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  cpp.spec "erase_end()" from source as erase_end_spec with (
    \prepost std.vector.specs "int" (std.allocator.T "int")
    \prepost std.vector.iterator.specs false "int" (std.allocator.T "int")
    \prepost std.vector.iterator.specs true "int" (std.allocator.T "int")
    \prepost std.vector.iterator.iter_to_const "int" (std.allocator.T "int")
    \prepost std.allocator.specs "int"
    \post emp).
  Lemma erase_end_ok : verify[source] erase_end_spec.
  Proof.
    verify_spec.
    rewrite /std.vector.specs /std.vector.iterator.specs /std.allocator.specs.
    go. Show. Fail Qed.
  Abort.
End with_cpp.
