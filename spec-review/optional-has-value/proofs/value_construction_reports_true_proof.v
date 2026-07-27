
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "value_construction_reports_true()" from test_cpp.source default.

  Lemma verify_value_construction_reports_true :
    verify[test_cpp.source] "value_construction_reports_true()".
  Proof.

    verify_spec.

    go $usenamed=true.

    (* Preserve the public optional state while deriving the reference fact required by destruction. *)
    wname [ (value_addr |-> optionalR 1$m (Some 5)) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists (1)%cQp, (Some 5).
    iFrame "Hvalue Href".
    go $usenamed=true.

    iExists (Some 5).
    go $usenamed=true.

  Qed.
End with_cpp.
