(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.

Require Import skylabs.brick.libstdcpp.test.vector.data_ub_cpp.

(** * The vector specs reject accesses through [data()] outside the elements

    Each client in [data_ub.cpp] gets stuck reading an element that the vector
    does not own; see data_ub_proof.expected. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  cpp.spec "data_past_end()" from source as data_past_end_spec with (
    \prepost std.vector.specs "int" (std.allocator.T "int")
    \prepost std.allocator.specs "int"
    \post{v}[Vint v] emp).
  Lemma data_past_end_ok : verify[source] data_past_end_spec.
  Proof. verify_spec; rewrite /std.vector.specs /std.allocator.specs; go. Show. Fail Qed. Abort.

  cpp.spec "data_empty()" from source as data_empty_spec with (
    \prepost std.vector.specs "int" (std.allocator.T "int")
    \prepost std.allocator.specs "int"
    \post{v}[Vint v] emp).
  Lemma data_empty_ok : verify[source] data_empty_spec.
  Proof. verify_spec; rewrite /std.vector.specs /std.allocator.specs; go. Show. Fail Qed. Abort.
End with_cpp.
