
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (MOD : test_cpp.source ⊧ σ).

  #[local] Instance inline_optional_move :
    ShouldInlineFunction
      "std::move<std::optional<int>&>(std::optional<int>&)"%cpp_name := {}.

  cpp.spec "move_construct_disengaged_stays_disengaged()"
    from test_cpp.source default.

  Lemma verify_move_construct_disengaged_stays_disengaged :
    verify[test_cpp.source] "move_construct_disengaged_stays_disengaged()".
  Proof.
    verify_spec.
    go $usenamed=true.

wname [ (source_addr |-> optionalR 1$m None) ] "Hsource".

iDestruct (observe (type_ptr optionalT source_addr) with "Hsource") as "#Htype".

iDestruct (type_ptr_reference_to with "Htype") as "#Href".

iExists (1)%cQp, None. iFrame "Hsource Href". go $usenamed=true.

iExists None. go $usenamed=true.

wname [ (destination_addr |-> optionalR 1$m None) ] "Hdestination".

iDestruct (observe (type_ptr optionalT destination_addr) with "Hdestination") as "#Hdestination_type".

iDestruct (type_ptr_reference_to with "Hdestination_type") as "#Hdestination_ref".

iExists (1)%cQp, None. iFrame "Hdestination Hdestination_ref". go $usenamed=true.

wname [ (source_addr |-> optionalR 1$m None) ] "Hsource_after_move".

iExists (1)%cQp, None. iFrame "Hsource_after_move". go $usenamed=true.

iExists None, None. go $usenamed=true.

Qed.

End with_cpp.
