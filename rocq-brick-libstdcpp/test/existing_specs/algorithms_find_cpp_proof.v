
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.algorithms_find_cpp.
Require Import skylabs.auto.cpp.prelude.test.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : algorithms_find_cpp.source ⊧ σ}.
  Import linearity.

  Section specs.
    cpp.spec "find_present_first_match()" as present_spec with
      (\post[Vint 7] emp).

    cpp.spec "find_missing_returns_end()" as missing_spec with
      (\post[Vbool true] emp).

    cpp.spec "find_in_subrange()" as subrange_spec with
      (\post[Vint 3] emp).

    cpp.spec "find_in_empty_range_returns_end()" as empty_spec with
      (\post[Vbool true] emp).

    cpp.spec "update_through_found_iterator()" as update_spec with
      (\post[Vint 31] emp).

    cpp.spec "main()" as main_spec with
      (\post[Vint 0] emp).
  End specs.

  #[local] Instance int_ptr_iterator_rep :
    concepts.BundledRep (Tptr "int") (ptr * Z) :=
    @concepts.Build_BundledRep _ _ Σ σ (Tptr "int") (ptr * Z)
      (fun q st => ptrR<"int"> q (st.1 .[ "int" ! st.2])).

  #[local] Instance int_ptr_has_ranges :
    std.HasRanges (Tptr "int") ptr Z :=
    std.array_ranges "int" (Tptr "int").

Lemma present_ok :
  std.find_spec (Tptr "int") "int" algorithms_find_cpp.source **
  std.cassert.assert_fail_spec |--
  verify[algorithms_find_cpp.source] present_spec.
Proof using MOD.
  verify_spec.

go $usenamed=true.

iExists values_addr, 0, 5, (1$m)%cQp, (1$m)%cQp, [4; 7; 7; 9; 11].

iFrame.

iDestruct select (values_addr |-> array_sliceR "int" 0 5 (fun v : Z => intR (1$m)%cQp v) [4; 7; 7; 9; 11]) as "A".
iDestruct (std.array_sliceR_eqv_spine_payload_rangeZ with "A") as "[A B]".

iFrame "A B".

go $usenamed=true.

iSplit; first by iPureIntro; rewrite offset_ptr_sub_0.

go $usenamed=true.

iDestruct select (std.payload (Tptr "int") values_addr (fun x : Z => intR (1$m)%cQp x) (rangeZ 0 5) [4; 7; 7; 9; 11]) as "P".

iEval (rewrite std.payload.unlock) in "P".

go $usenamed=true.

Qed.
Lemma missing_ok :
  std.find_spec (Tptr "int") "int" algorithms_find_cpp.source **
  std.cassert.assert_fail_spec |--
  verify[algorithms_find_cpp.source] missing_spec.
Proof using MOD.
  verify_spec.
  go $usenamed=true.
  iExists values_addr, 0, 4, (1$m)%cQp, (1$m)%cQp, [4; 7; 9; 11].
  iFrame.
  iDestruct select (values_addr |-> array_sliceR "int" 0 4 (fun v : Z => intR (1$m)%cQp v) [4; 7; 9; 11]) as "A".
  iDestruct (std.array_sliceR_eqv_spine_payload_rangeZ with "A") as "[A B]".
  iFrame "A B".
  go $usenamed=true.
  iSplit; first by iPureIntro; rewrite offset_ptr_sub_0.
  go $usenamed=true.
  iDestruct select (std.payload (Tptr "int") values_addr (fun x : Z => intR (1$m)%cQp x) (rangeZ 0 4) [4; 7; 9; 11]) as "P".
  iEval (rewrite std.payload.unlock) in "P".
  go $usenamed=true.
Qed.

Lemma subrange_ok :
  std.find_spec (Tptr "int") "int" algorithms_find_cpp.source **
  std.cassert.assert_fail_spec |--
  verify[algorithms_find_cpp.source] subrange_spec.
Proof using MOD.
  verify_spec.
  go $usenamed=true.
  iDestruct select (values_addr |-> array_sliceR "int" 0 5 (fun v : Z => intR (1$m)%cQp v) [3; 5; 3; 8; 3]) as "A".
  iDestruct (array_sliceR_cons with "A") as "[[#T P] A]".
  iExists values_addr, 1, 5, (1$m)%cQp, (1$m)%cQp, [5; 3; 8; 3].
  iFrame.
  iDestruct (std.array_sliceR_eqv_spine_payload_rangeZ with "A") as "[A B]".
  iFrame "A B".
  go $usenamed=true.
  iDestruct select (std.payload (Tptr "int") values_addr (fun x : Z => intR (1$m)%cQp x) (rangeZ 1 5) [5; 3; 8; 3]) as "P1".
  iEval (rewrite std.payload.unlock) in "P1".
  go $usenamed=true.
Qed.

Lemma empty_ok :
  std.find_spec (Tptr "int") "int" algorithms_find_cpp.source **
  std.cassert.assert_fail_spec |--
  verify[algorithms_find_cpp.source] empty_spec.
Proof using MOD.
  verify_spec.
  go $usenamed=true.
  iExists values_addr, 1, 1, (1$m)%cQp, (1$m)%cQp, ([] : list Z).
  iFrame.
  go $usenamed=true.
  rewrite /std.array_spine.
  rewrite std.payload.unlock.
  go $usenamed=true.
  rewrite rangeZ_nil /=.
  go $usenamed=true.
Qed.

Lemma update_ok :
  std.find_spec (Tptr "int") "int" algorithms_find_cpp.source **
  std.cassert.assert_fail_spec |--
  verify[algorithms_find_cpp.source] update_spec.
Proof using MOD.
  verify_spec.
  go $usenamed=true.
  iExists values_addr, 0, 4, (1$m)%cQp, (1$m)%cQp, [10; 20; 30; 40].
  iFrame.
  iDestruct select (values_addr |-> array_sliceR "int" 0 4 (fun v : Z => intR (1$m)%cQp v) [10; 20; 30; 40]) as "A".
  iDestruct (std.array_sliceR_eqv_spine_payload_rangeZ with "A") as "[A B]".
  iFrame "A B".
  go $usenamed=true.
  iSplit; first by iPureIntro; rewrite offset_ptr_sub_0.
  go $usenamed=true.
  iDestruct select (std.payload (Tptr "int") values_addr (fun x : Z => intR (1$m)%cQp x) (rangeZ 0 4) [10; 20; 30; 40]) as "P".
  iEval (rewrite std.payload.unlock) in "P".
  go $usenamed=true.
Qed.

Definition present_B := [LINK] present_ok.
Definition missing_B := [LINK] missing_ok.
Definition subrange_B := [LINK] subrange_ok.
Definition empty_B := [LINK] empty_ok.
Definition update_B := [LINK] update_ok.

#[local] Hint Resolve present_B missing_B subrange_B empty_B update_B : sl_opacity.

Lemma main_ok :
  std.find_spec (Tptr "int") "int" algorithms_find_cpp.source **
  std.cassert.assert_fail_spec |--
  verify[algorithms_find_cpp.source] main_spec.
Proof using MOD.
  verify_spec.
  go $usenamed=true.
Qed.

End with_cpp.

Section boundary_evidence.
  Context `{Σ : cpp_logic, σ : genv}.
  Import linearity.

  (* A reversed pointer interval cannot satisfy the frozen find range resource. *)
  Lemma reversed_find_range_unreachable
      (basep : ptr) (q : cQp.t) (first last : Z) (indices : list Z) :
    last < first ->
    std.array_spine "int" basep q first indices last |-- [| False |].
  Proof.
    intros Hreversed.
    rewrite /std.array_spine.

go $usenamed=true.

iPureIntro. lia.

Qed.

  (* The frozen payload indexes only [first,last), so end cannot be dereferenced. *)
  Lemma find_end_is_not_payload_index (first last : Z) :
    last ∈ rangeZ first last -> False.
  Proof.
    intros Hend.
    apply elem_of_rangeZ in Hend.
    lia.
  Qed.
End boundary_evidence.

