
Require Import skylabs.brick.libstdcpp.test.optional.clients_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : !clients_cpp.source ⊧ σ}.
  cpp.spec "__assert_fail" from clients_cpp.source
    as assert_fail_unreachable_spec with (
      \with{assertion file function_name : ptr} {line : Z}
      \arg{assertion} "__assertion" (Vptr assertion)
      \arg{file} "__file" (Vptr file)
      \arg{line} "__line" (Vint line)
      \arg{function_name} "__function" (Vptr function_name)
      \pre [| False |]
      \post emp
    ).

  cpp.spec "byte_one_and_max_are_preserved()" from clients_cpp.source
    as byte_one_and_max_are_preserved_spec with (\post emp).
  
  
  #[global] Instance optional_uint8_value_rvalue_ctor_client_spec_instance :
    SpecFor clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)" :=
    SpecFor.mk clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)"
      optional_uint8_value_rvalue_ctor_spec.


Lemma byte_one_and_max_are_preserved_proof :
  verify[clients_cpp.module] "byte_one_and_max_are_preserved()".
  try rewrite /optional_uint8_has_value_template_spec.
  try rewrite /optional_uint8_deref_const_lvalue_template_spec.
  try rewrite /optional_uint8_destructor_template_spec.
  try rewrite /assert_fail_unreachable_spec.

  Proof using MOD.
    rewrite /optional_uint8_value_rvalue_ctor_spec
      /optional_uint8_has_value_spec
      /optional_uint8_deref_const_lvalue_spec
      /optional_uint8_destructor_spec.
    verify_spec.
repeat first [ progress (go) | iExists _; iFrame | rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ _ _ _)) ].

  Qed.
End with_cpp.
