
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "emplace_then_query_reports_true()" from test_cpp.source default.

  Lemma verify_emplace_then_query_reports_true :
    verify[test_cpp.source] "emplace_then_query_reports_true()".
  Proof.
    verify_spec.
    go $usenamed=true.

    (* Preserve the optional state while deriving the reference fact needed by emplace and destruction. *)
    wname [ (value_addr |-> optionalR 1$m None) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    go $usenamed=true.

    iExists None.
    iFrame "Hvalue".
    go $usenamed=true.

    iExists (1)%cQp, (Some 7).
    go $usenamed=true.

    iExists (Some 7).
    go $usenamed=true.
  Qed.
End with_cpp.
