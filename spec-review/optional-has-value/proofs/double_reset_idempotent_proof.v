Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "double_reset_idempotent()" from test_cpp.source default.

  Lemma verify_double_reset_idempotent :
    verify[test_cpp.source] "double_reset_idempotent()".
  Proof.
    verify_spec.
    go $usenamed=true.
    wname [ (value_addr |-> optionalR 1$m None) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists None.
    iFrame "Hvalue Href".
    go $usenamed=true.
    iExists (1)%cQp, None.
    go $usenamed=true.
    iExists None.
    go $usenamed=true.
    iExists (1)%cQp, None.
    go $usenamed=true.
    iExists None.
    go $usenamed=true.
  Qed.
End with_cpp.

