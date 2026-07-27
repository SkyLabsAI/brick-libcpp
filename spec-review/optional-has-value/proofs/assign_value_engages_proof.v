
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "assign_value_engages()" from test_cpp.source default.

  Lemma verify_assign_value_engages :
    verify[test_cpp.source] "assign_value_engages()".
  Proof.
    verify_spec.
    go $usenamed=true.

    wname [ (value_addr |-> optionalR 1$m None) ] "Hdst".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hdst") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists (Some 7), None.
    iFrame "Hdst Href".
    go $usenamed=true.

    iExists (Some 7).
    go $usenamed=true.

    iExists (1)%cQp, (Some 7).
    go $usenamed=true.
    iExists (Some 7).
    go $usenamed=true.
  Qed.
End with_cpp.
