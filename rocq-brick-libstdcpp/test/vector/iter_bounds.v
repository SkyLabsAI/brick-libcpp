(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.test.vector.iter_bounds_cpp.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.

(** * Vector iterators must be dereferenceable for [*it] and [++it]

    Both require [it] to be dereferenceable ([input.iterators];
    [iterator.requirements.general]/7: "The library never assumes that
    past-the-end values are dereferenceable"). [deref_empty] and
    [inc_past_end] violate this; [_GLIBCXX_DEBUG] reports both, and UBSan
    reports both here because an empty vector's iterators are null. *)
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "deref_first()" from source as deref_first_spec with (\post[Vint 7] emp).
  cpp.spec "inc_to_end()" from source as inc_to_end_spec with (\post emp).
  cpp.spec "deref_empty()" from source as deref_empty_spec with (\post[Vbool true] emp).
  cpp.spec "inc_past_end()" from source as inc_past_end_spec with (\post emp).

  (* The [iExists] steps give the model of an iterator to its destructor. *)
  Lemma deref_first_ok : verify[source] deref_first_spec.
  Proof.
    verify_spec; go.
    iExists (_, _). iFrame. iIntros "?". go.
  Qed.

  Lemma inc_to_end_ok : verify[source] inc_to_end_spec.
  Proof.
    verify_spec; go.
    iExists (_, _). iFrame. go.
  Qed.

  (** An empty vector's iterators are null, so the obligation that both
      negative cases below get stuck on is false. *)
  Lemma null_not_dereferenceable : type_ptr "int" (nullptr .[ "int" ! 0 ]) ⊢ False.
  Proof. rewrite type_ptr_off_nonnull. by iIntros "%". Qed.

  (** Stuck at [*v.begin()] on [type_ptr "int" (nullptr .[ "int" ! 0 ])]. *)
  Lemma deref_empty_ok : verify[source] deref_empty_spec.
  Proof. verify_spec; go. Fail Qed. Abort.

  (** Stuck at [++e] on [type_ptr "int" (nullptr .[ "int" ! 0 ])]: [v.end()] is
      past the end. *)
  Lemma inc_past_end_ok : verify[source] inc_past_end_spec.
  Proof. verify_spec; go. Fail Qed. Abort.
End with_cpp.
