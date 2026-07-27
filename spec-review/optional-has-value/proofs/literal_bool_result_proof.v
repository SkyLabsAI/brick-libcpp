
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "literal_bool_result()" from test_cpp.source with
    (\prepost _global "std::nullopt" |-> structR nulloptN 1$m
     \post emp).

  Lemma verify_literal_bool_result :
    verify[test_cpp.source] "literal_bool_result()".
  Proof.
    verify_spec'.
    iClear select (▷ (_global "std::nullopt" |-> structR nulloptN 1$c))%I.
    repeat iRevert select (▷ _)%I.
    repeat iIntros "#?".
    iModIntro. iIntros (POST vals) "Hpre".
    go $usenamed=true.
    wname [ (engaged_addr |-> optionalR 1$m (Some 5)) ] "Heng".
    iDestruct (observe (type_ptr optionalT engaged_addr) with "Heng") as "#Htype_e".
    iDestruct (type_ptr_reference_to with "Htype_e") as "#Href_e".
    iExists (1)%cQp, (Some 5).
    iFrame "Heng Href_e".
    go $usenamed=true.
    wname [ (disengaged_addr |-> optionalR 1$m None) ] "Hdis".
    iDestruct (observe (type_ptr optionalT disengaged_addr) with "Hdis") as "#Htype_d".
    iDestruct (type_ptr_reference_to with "Htype_d") as "#Href_d".
    iExists (1)%cQp, None.
    iFrame "Hdis Href_d".
    go $usenamed=true.
    wname [ (engaged_addr |-> optionalR 1$m (Some 5)) ] "Heng2".
    iExists (1)%cQp, (Some 5).
    iFrame "Heng2".
    go $usenamed=true.
    wname [ (disengaged_addr |-> optionalR 1$m None) ] "Hdis2".
    iExists (1)%cQp, None.
    iFrame "Hdis2".
    go $usenamed=true.
    iExists None, (Some 5).
    go $usenamed=true.
  Qed.
End with_cpp.
