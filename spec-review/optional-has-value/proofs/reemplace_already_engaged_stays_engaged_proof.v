
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "reemplace_already_engaged_stays_engaged()" from test_cpp.source default.

  Lemma verify_reemplace_already_engaged_stays_engaged :
    verify[test_cpp.source] "reemplace_already_engaged_stays_engaged()".
  Proof.
    verify_spec.
    go $usenamed=true.

    wname [ (value_addr |-> optionalR 1$m (Some 3)) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists (1)%cQp, (Some 3).
    iFrame "Hvalue Href".
    go $usenamed=true.

    iExists (Some 3).
    go $usenamed=true.

    iExists (1)%cQp, (Some 9).
    go $usenamed=true.

    iExists (Some 9).
    go $usenamed=true.
  Qed.
End with_cpp.
