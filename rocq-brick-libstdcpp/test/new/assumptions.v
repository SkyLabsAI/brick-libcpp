Require Import skylabs.auto.cpp.prelude.proof.
Require skylabs.brick.libstdcpp.new.consistency.
Require skylabs.brick.libstdcpp.test.new.demo_cpp_proof.

(** Assumption gate for the new/delete evidence: the expected output lists
    every axiom the consistency lemma and the end-to-end tests rely on.
    A new admit or axiom anywhere underneath changes it. *)
Definition new_delete_evidence :=
  (@consistency.wp_new_aligned_token,
   @demo_cpp_proof.test_new_ok,
   @demo_cpp_proof.test_delete_ok,
   @demo_cpp_proof.test_new_delete_ok,
   @demo_cpp_proof.test_delete_array_ok,
   @demo_cpp_proof.test_new_array_ok,
   @demo_cpp_proof.test_new_delete_array_ok,
   @demo_cpp_proof.test_raw_scalar_ok,
   @demo_cpp_proof.test_raw_scalar_sized_ok,
   @demo_cpp_proof.test_raw_array_ok,
   @demo_cpp_proof.test_raw_array_sized_ok,
   @demo_cpp_proof.test_raw_scalar_nothrow_ok,
   @demo_cpp_proof.test_raw_array_nothrow_ok,
   @demo_cpp_proof.test_raw_delete_null_ok,
   @demo_cpp_proof.test_raw_scalar_aligned_ok,
   @demo_cpp_proof.test_raw_scalar_aligned_sized_ok,
   @demo_cpp_proof.test_raw_scalar_aligned_nothrow_ok,
   @demo_cpp_proof.test_raw_array_aligned_ok,
   @demo_cpp_proof.test_raw_array_aligned_sized_ok,
   @demo_cpp_proof.test_raw_array_aligned_nothrow_ok,
   @demo_cpp_proof.test_raw_aligned_delete_null_ok,
   @demo_cpp_proof.aligned_value_dtor_ok,
   @demo_cpp_proof.test_new_delete_aligned_ok,
   @demo_cpp_proof.test_delete_aligned_ok,
   @demo_cpp_proof.test_delete_null_aligned_ok,
   @demo_cpp_proof.test_raw_scalar_zero_ok,
   @demo_cpp_proof.test_raw_array_zero_ok,
   @demo_cpp_proof.test_raw_scalar_aligned_zero_ok,
   @demo_cpp_proof.test_raw_array_aligned_zero_ok,
   @demo_cpp_proof.test_new_nothrow_delete_ok,
   @demo_cpp_proof.test_new_nothrow_aligned_delete_ok,
   @demo_cpp_proof.test_delete_null_ok,
   @demo_cpp_proof.test_new_aligned_token_ok,
   @demo_cpp_proof.test_new_delete_array_dtor_ok,
   @demo_cpp_proof.test_new_delete_aligned_array_ok,
   @demo_cpp_proof.test_new_delete_aligned_array_dtor_ok).

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
Print Assumptions new_delete_evidence.
