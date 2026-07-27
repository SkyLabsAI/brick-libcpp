Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.bad_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : bad_cpp.source ⊧ σ}.

  cpp.spec "bad_default_optional_reports_true()" from bad_cpp.source default.

  (* Adversarial probe: a default-constructed [std::optional<int>] is disengaged,
     so [has_value()] is [false]. This client asserts it is [true]. Under the
     sound observer contract the failing assert forces the unreachable
     [__assert_fail] branch, whose precondition is [False]; discharging it is
     impossible, so the proof cannot close and THIS BUILD MUST FAIL. A build
     failure here is the intended negative evidence that the frozen spec forbids
     the bad conclusion. If a future weakening of the observer spec ever let the
     bad result be derived, [go] would close the goal, [Qed] would succeed, and
     the judge would reject the spec. *)
  Lemma verify_bad_default_optional_reports_true :
    verify[bad_cpp.source] "bad_default_optional_reports_true()".
  Proof.
    verify_spec.
    go $usenamed=true.
    wname [ (value_addr |-> optionalR 1$m None) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists (1)%cQp, None.
    iFrame "Hvalue Href".
    go $usenamed=true.
  Qed.
End with_cpp.
