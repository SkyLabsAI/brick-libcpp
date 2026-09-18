(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.all_any_none_of.spec.
Require Import skylabs.brick.libstdcpp.test.all_any_none_of.test_cpp.

#[local] Set Default Goal Selector "!".

Require Import skylabs.brick.libstdcpp.test.all_any_none_of.test_cpp_proof_prelude.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  #[local] Hint Resolve is_nonzero_predicate_spec_C : br_hints.
  #[local] Hint Resolve is_seven_predicate_spec_C : br_hints.
  #[local] Hint Resolve is_zero_predicate_spec_C : br_hints.
  #[local] Hint Resolve has_high_bit_predicate_spec_C : br_hints.

  #[local] Hint Resolve
    array.array_sliceR_matching_prefix_l_C
    array.array_sliceR_matching_prefix_r_C
    array.array_sliceR_matching_suffix_l_C
    array.array_sliceR_matching_suffix_r_C : br_hints.

  #[local] Hint Resolve
    array.array_sliceR_matching_prefix_l_C'
    array.array_sliceR_matching_prefix_r_C'
    array.array_sliceR_matching_suffix_l_C'
    array.array_sliceR_matching_suffix_r_C' : br_hints.

  Ltac use_is_nonzero :=
    iExists (fun x => Some (bool_decide (x <> 0)%Z)), (fun _ => emp); go.
  Ltac use_is_seven :=
    iExists (fun x => Some (bool_decide (x = 7)%Z)), (fun _ => emp); go.
  Ltac use_is_zero :=
    iExists (fun x => Some (bool_decide (x = 0)%Z)), (fun _ => emp); go.
  Ltac use_has_high_bit :=
    iExists (fun x => Some (bool_decide (128 <= x)%Z)), (fun _ => emp); go.
  Context {MOD : test_cpp.source ⊧ σ}.

  cpp.spec "unsigned_high_bit_predicate_results()" default.
  Lemma unsigned_high_bit_predicate_results_ok :
    verify[test_cpp.source] "unsigned_high_bit_predicate_results()".
  Proof using MOD.
    verify_spec; go.
    repeat use_has_high_bit.
  Qed.

End with_cpp.
