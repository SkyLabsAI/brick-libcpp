
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (MOD : test_cpp.source ⊧ σ).

  cpp.spec "disengaged_construction_reports_false()" from test_cpp.source with
    (\prepost _global "std::nullopt" |-> structR nulloptN 1$m
     \post emp).

  Lemma verify_disengaged_construction_reports_false :
    verify[test_cpp.source] "disengaged_construction_reports_false()".
  Proof.
    verify_spec'.
    iClear select (▷ (_global "std::nullopt" |-> structR nulloptN 1$c))%I.
    repeat iRevert select (▷ _)%I.
    repeat iIntros "#?".
    iModIntro. iIntros (POST vals) "Hpre".
    go $usenamed=true.
    wname [ (default_constructed_addr |-> optionalR 1$m None) ] "Hdefault".
    iDestruct (observe (type_ptr optionalT default_constructed_addr) with "Hdefault") as "#Htype1".
    iDestruct (type_ptr_reference_to with "Htype1") as "#Href1".
    iExists (1)%cQp, None.
    iFrame "Hdefault Href1".
    go $usenamed=true.
    wname [ (nullopt_constructed_addr |-> optionalR 1$m None) ] "Hnullopt".
    iDestruct (observe (type_ptr optionalT nullopt_constructed_addr) with "Hnullopt") as "#Htype2".
    iDestruct (type_ptr_reference_to with "Htype2") as "#Href2".
    iExists (1)%cQp, None.
    iFrame "Hnullopt Href2".
    go $usenamed=true.
    iExists None, None.
    go $usenamed=true.
  Qed.
End with_cpp.
