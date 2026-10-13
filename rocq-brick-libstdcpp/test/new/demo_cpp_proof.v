Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.hints.alignment.
Require Import skylabs.brick.libstdcpp.new.pred.

Require Import skylabs.brick.libstdcpp.new.spec_exc.
Require Import skylabs.brick.libstdcpp.new.hints.
Require skylabs.brick.libstdcpp.test.new.demo_cpp.

sl.lock
Definition AlignedValueR `{Σ : cpp_logic} {σ : genv}
    (q : cQp.t) (value : Z) : Rep :=
  structR "AlignedValue" q **
  _field "AlignedValue::value" |-> intR q value.
#[only(cfracsplittable,type_ptr,lazy_unfold(global))] derive AlignedValueR.

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


  (* Aligned allocation must keep its exact alignment argument. *)
  cpp.spec "test_raw_scalar_aligned(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_scalar_aligned_ok : verify[demo_cpp.source] "test_raw_scalar_aligned(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_scalar_aligned_sized(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_scalar_aligned_sized_ok : verify[demo_cpp.source] "test_raw_scalar_aligned_sized(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_scalar_aligned_nothrow(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_scalar_aligned_nothrow_ok : verify[demo_cpp.source] "test_raw_scalar_aligned_nothrow(enum std::align_val_t)".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  cpp.spec "test_raw_array_aligned(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_array_aligned_ok : verify[demo_cpp.source] "test_raw_array_aligned(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_array_aligned_sized(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_array_aligned_sized_ok : verify[demo_cpp.source] "test_raw_array_aligned_sized(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_array_aligned_nothrow(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_array_aligned_nothrow_ok : verify[demo_cpp.source] "test_raw_array_aligned_nothrow(enum std::align_val_t)".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  cpp.spec "test_raw_aligned_delete_null(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al) \post emp).
  Lemma test_raw_aligned_delete_null_ok : verify[demo_cpp.source] "test_raw_aligned_delete_null(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_scalar_to_aligned_delete()" from demo_cpp.source with
    (\post emp).
  Lemma test_scalar_to_aligned_delete_rejected : verify[demo_cpp.source] "test_scalar_to_aligned_delete()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_aligned_scalar_to_unaligned_delete(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_aligned_scalar_to_unaligned_delete_rejected : verify[demo_cpp.source] "test_aligned_scalar_to_unaligned_delete(enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_scalar_to_aligned_delete_sized()" from demo_cpp.source with
    (\post emp).
  Lemma test_scalar_to_aligned_delete_sized_rejected : verify[demo_cpp.source] "test_scalar_to_aligned_delete_sized()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_aligned_scalar_to_unaligned_delete_sized(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_aligned_scalar_to_unaligned_delete_sized_rejected : verify[demo_cpp.source] "test_aligned_scalar_to_unaligned_delete_sized(enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_scalar_wrong_alignment(void*, enum std::align_val_t)" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \arg{al} "al" (Vn al)
     \pre{original} p |-> (blockR 16 1$m ** alignedR al **
                             allocatedR 1 false (Some original) 16)
     \require original <> al
     \post emp).
  Lemma test_scalar_wrong_alignment_rejected : verify[demo_cpp.source] "test_scalar_wrong_alignment(void*, enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_scalar_wrong_alignment_sized(void*, enum std::align_val_t)" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \arg{al} "al" (Vn al)
     \pre{original} p |-> (blockR 16 1$m ** alignedR al **
                             allocatedR 1 false (Some original) 16)
     \require original <> al
     \post emp).
  Lemma test_scalar_wrong_alignment_sized_rejected : verify[demo_cpp.source] "test_scalar_wrong_alignment_sized(void*, enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_to_aligned_delete()" from demo_cpp.source with
    (\post emp).
  Lemma test_array_to_aligned_delete_rejected : verify[demo_cpp.source] "test_array_to_aligned_delete()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_aligned_array_to_unaligned_delete(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_aligned_array_to_unaligned_delete_rejected : verify[demo_cpp.source] "test_aligned_array_to_unaligned_delete(enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_to_aligned_delete_sized()" from demo_cpp.source with
    (\post emp).
  Lemma test_array_to_aligned_delete_sized_rejected : verify[demo_cpp.source] "test_array_to_aligned_delete_sized()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_aligned_array_to_unaligned_delete_sized(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_aligned_array_to_unaligned_delete_sized_rejected : verify[demo_cpp.source] "test_aligned_array_to_unaligned_delete_sized(enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_wrong_alignment(void*, enum std::align_val_t)" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \arg{al} "al" (Vn al)
     \pre{original} p |-> (blockR 16 1$m ** alignedR al **
                             allocatedR 1 true (Some original) 16)
     \require original <> al
     \post emp).
  Lemma test_array_wrong_alignment_rejected : verify[demo_cpp.source] "test_array_wrong_alignment(void*, enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_wrong_alignment_sized(void*, enum std::align_val_t)" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \arg{al} "al" (Vn al)
     \pre{original} p |-> (blockR 16 1$m ** alignedR al **
                             allocatedR 1 true (Some original) 16)
     \require original <> al
     \post emp).
  Lemma test_array_wrong_alignment_sized_rejected : verify[demo_cpp.source] "test_array_wrong_alignment_sized(void*, enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "AlignedValue::~AlignedValue()" from demo_cpp.source with
    (\this this
     \pre{value} this |-> AlignedValueR 1$m value
     \post emp).
  Lemma aligned_value_dtor_ok : verify[demo_cpp.source] "AlignedValue::~AlignedValue()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_new_delete_aligned()" from demo_cpp.source with (\post emp).
  Lemma test_new_delete_aligned_ok : verify[demo_cpp.source] "test_new_delete_aligned()".
  Proof.
    verify_spec; go.
    iSplitR.
    { iPureIntro. exists ("AlignedValue"%cpp_type).
      apply (@_align_of_ok demo_cpp.source σ _). vm_compute. reflexivity. }
    go.
  Qed.

  cpp.spec "test_raw_scalar_zero()" from demo_cpp.source with (\post emp).
  Lemma test_raw_scalar_zero_ok : verify[demo_cpp.source] "test_raw_scalar_zero()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_array_zero()" from demo_cpp.source with (\post emp).
  Lemma test_raw_array_zero_ok : verify[demo_cpp.source] "test_raw_array_zero()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_scalar_aligned_zero(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_scalar_aligned_zero_ok : verify[demo_cpp.source] "test_raw_scalar_aligned_zero(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_raw_array_aligned_zero(enum std::align_val_t)" from demo_cpp.source with
    (\arg{al} "al" (Vn al)
     \require supported_alignment al
     \post emp).
  Lemma test_raw_array_aligned_zero_ok : verify[demo_cpp.source] "test_raw_array_aligned_zero(enum std::align_val_t)".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_scalar_zero_to_aligned_delete()" from demo_cpp.source with (\post emp).
  Lemma test_scalar_zero_to_aligned_delete_rejected : verify[demo_cpp.source] "test_scalar_zero_to_aligned_delete()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_array_zero_to_aligned_delete()" from demo_cpp.source with (\post emp).
  Lemma test_array_zero_to_aligned_delete_rejected : verify[demo_cpp.source] "test_array_zero_to_aligned_delete()".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_raw_scalar_partial_receipt(void*, enum std::align_val_t)" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \arg{al} "al" (Vn al)
     \pre p |-> (blockR 16 1$m ** alignedR al **
                 allocatedR (1 / 2)%Qp false (Some al) 16)
     \post emp).
  Lemma test_raw_scalar_partial_receipt_rejected : verify[demo_cpp.source] "test_raw_scalar_partial_receipt(void*, enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

  cpp.spec "test_raw_array_partial_receipt(void*, enum std::align_val_t)" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \arg{al} "al" (Vn al)
     \pre p |-> (blockR 16 1$m ** alignedR al **
                 allocatedR (1 / 2)%Qp true (Some al) 16)
     \post emp).
  Lemma test_raw_array_partial_receipt_rejected : verify[demo_cpp.source] "test_raw_array_partial_receipt(void*, enum std::align_val_t)".
  Proof. verify_spec; go. Fail Qed. Abort.

End with_cpp.
