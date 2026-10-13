Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.new.pred.

Require Import skylabs.brick.libstdcpp.new.spec_exc.
Require Import skylabs.brick.libstdcpp.new.hints.
Require skylabs.brick.libstdcpp.test.new.demo_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Import linearity.

  cpp.spec "test_new()" from demo_cpp.source with
    (\post{p}[Vptr p]
       p |-> (intR 1$m 0 ** alloc.tokenR "int" 1)).

  Lemma test_new_ok : verify[demo_cpp.source] "test_new()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_delete(int* )" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \pre{v} p |-> (intR 1$m v ** alloc.tokenR "int" 1)
     \post emp).

  Lemma test_delete_ok : verify[demo_cpp.source] "test_delete(int* )".
  Proof.
    verify_spec.
    go; case_bool_decide; go.
  Qed.

  cpp.spec "test_new_delete()" from demo_cpp.source with
    (\post emp).

  Lemma test_new_delete_ok : verify[demo_cpp.source] "test_new_delete()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_new_array()" from demo_cpp.source with
    (\post{p}[Vptr p]
      p |-> (array_sliceR "int" 0 2 (fun z => intR 1$m z) [1; 2]%Z **
      alloc.tokenR "int[2]" 1)
    ).

  cpp.spec "test_delete_array(int* )" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \pre p |-> (array_sliceR "int" 0 2 (fun z => intR 1$m z) [1; 2]%Z **
                 alloc.tokenR "int[2]" 1)
     \post emp
    ).

  cpp.spec "test_new_delete_array()" from demo_cpp.source with
    (\post emp).

  Lemma test_delete_array_ok : verify[demo_cpp.source] "test_delete_array(int* )".
  Proof.
    verify_spec; go.
  Qed.

  (** The C++ standard recommends <<262144 <= SIZE_MAX>>.  *)
  Axiom Cpp_SIZE_MAX : (262144 <= SIZE_MAX)%N.

  Lemma test_new_array_ok : verify[demo_cpp.source] "test_new_array()".
  Proof.
    verify_spec.
    go.
    { exfalso.
      generalize Cpp_SIZE_MAX. lia. }
    { normalize_ptrs.
      rewrite Z.add_opp_diag_r. normalize_ptrs. go. }
  Qed.

  Lemma test_new_delete_array_ok : verify[demo_cpp.source] "test_new_delete_array()".
  Proof.
    verify_spec; go.
    normalize_ptrs.
    rewrite Z.add_opp_diag_r. normalize_ptrs.
    go.
  Qed.

  cpp.spec "test_raw_scalar()" from demo_cpp.source with (\post emp).
  Lemma test_raw_scalar_ok : verify[demo_cpp.source] "test_raw_scalar()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_scalar_sized()" from demo_cpp.source with (\post emp).
  Lemma test_raw_scalar_sized_ok : verify[demo_cpp.source] "test_raw_scalar_sized()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_array()" from demo_cpp.source with (\post emp).
  Lemma test_raw_array_ok : verify[demo_cpp.source] "test_raw_array()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_array_sized()" from demo_cpp.source with (\post emp).
  Lemma test_raw_array_sized_ok : verify[demo_cpp.source] "test_raw_array_sized()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_scalar_nothrow()" from demo_cpp.source with (\post emp).
  Lemma test_raw_scalar_nothrow_ok : verify[demo_cpp.source] "test_raw_scalar_nothrow()".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  cpp.spec "test_raw_array_nothrow()" from demo_cpp.source with (\post emp).
  Lemma test_raw_array_nothrow_ok : verify[demo_cpp.source] "test_raw_array_nothrow()".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  cpp.spec "test_raw_delete_null()" from demo_cpp.source with (\post emp).
  Lemma test_raw_delete_null_ok : verify[demo_cpp.source] "test_raw_delete_null()".
  Proof. verify_spec; go. Qed.

  (* If a mismatched pair ever verifies again, [Fail Qed] rejects the test. *)
  cpp.spec "test_scalar_to_array_delete()" from demo_cpp.source with (\post emp).
  Lemma test_scalar_to_array_delete_rejected :
    verify[demo_cpp.source] "test_scalar_to_array_delete()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_scalar_to_array_delete_sized()" from demo_cpp.source with (\post emp).
  Lemma test_scalar_to_array_delete_sized_rejected :
    verify[demo_cpp.source] "test_scalar_to_array_delete_sized()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_to_scalar_delete()" from demo_cpp.source with (\post emp).
  Lemma test_array_to_scalar_delete_rejected :
    verify[demo_cpp.source] "test_array_to_scalar_delete()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_to_scalar_delete_sized()" from demo_cpp.source with (\post emp).
  Lemma test_array_to_scalar_delete_sized_rejected :
    verify[demo_cpp.source] "test_array_to_scalar_delete_sized()".
  Proof. verify_spec; go. Fail Qed. Abort.

End with_cpp.
