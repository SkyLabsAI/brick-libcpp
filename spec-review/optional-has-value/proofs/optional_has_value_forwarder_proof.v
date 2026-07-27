Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

(* The test-local free forwarder [bool has_value(const std::optional<int>&)]
   returns exactly the engagement bit the member [has_value] reports. Its
   contract is proved here directly from the frozen member observer spec (no
   assumption), and registered on the translation unit so the clients that pin
   [has_value(o)] discharge their asserts through the member's own contract. *)
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (MOD : test_cpp.source ⊧ σ).

  cpp.spec "has_value(std::optional<int> const&)" from test_cpp.source
    as optional_has_value_forwarder_spec with (
      \arg{op} "o" (Vref op)
      \prepost{q st} op |-> optionalR q st
      \post[Vbool (is_engaged st)] emp
    ).

  Lemma verify_optional_has_value_forwarder :
    verify[test_cpp.source] "has_value(std::optional<int> const&)".
  Proof.
    verify_spec.
    go $usenamed=true.
    iExists q, st.
    iFrame.
    go $usenamed=true.
  Qed.
End with_cpp.
