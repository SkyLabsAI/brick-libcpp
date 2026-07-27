
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.
Require Import skylabs.brick.libstdcpp.test.optional.optional_has_value_forwarder_proof.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (MOD : test_cpp.source ⊧ σ).

  cpp.spec "copy_construct_disengaged()" from test_cpp.source default.

  Lemma verify_copy_construct_disengaged :
    verify[test_cpp.source] "copy_construct_disengaged()".
  Proof.
    verify_spec.
    go $usenamed=true.
    wname [ (source_addr |-> optionalR 1$m None) ] "Hsource".
    iDestruct (observe (type_ptr optionalT source_addr) with "Hsource") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists (1)%cQp, None.
    iFrame "Hsource Href".
    go $usenamed=true.
    wname [ (destination_addr |-> optionalR 1$m None) ] "Hdestination".
    iDestruct (observe (type_ptr optionalT destination_addr) with "Hdestination") as "#Hdestination_type".
    iDestruct (type_ptr_reference_to with "Hdestination_type") as "#Hdestination_ref".
    iExists (1)%cQp, None.
    iFrame "Hdestination Hdestination_ref".
    go $usenamed=true.
    iExists None, None.
    go $usenamed=true.
  Qed.
End with_cpp.
