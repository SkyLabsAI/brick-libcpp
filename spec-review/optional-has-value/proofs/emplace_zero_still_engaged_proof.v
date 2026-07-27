
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "emplace_zero_still_engaged()" from test_cpp.source default.

  Lemma verify_emplace_zero_still_engaged :
    verify[test_cpp.source] "emplace_zero_still_engaged()".
  Proof.
    verify_spec.
    go $usenamed=true.
    wname [ (value_addr |-> optionalR 1$m (Some 5)) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    go $usenamed=true.
    iExists (Some 5).
    iFrame "Hvalue".
    go $usenamed=true.
    iExists (1)%cQp, (Some 0).
    go $usenamed=true.
    iExists (Some 0).
    go $usenamed=true.
  Qed.
End with_cpp.
