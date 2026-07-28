
Require Import skylabs.brick.libstdcpp.test.optional.clients_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.optional.hints.
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

  
  #[global] Instance optional_uint8_value_lvalue_ctor_client_spec_instance :
    SpecFor clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)" :=
    SpecFor.mk clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)"
      optional_uint8_value_lvalue_ctor_spec.


  cpp.spec "check_named_lvalue_roundtrip(unsigned char)"
    from clients_cpp.source as check_named_lvalue_roundtrip_helper_spec with (
      \with{b : Z}
      \arg{b} "b" (Vint b)
      \post emp
    ).

  cpp.spec "named_lvalue_parameterized_roundtrip()"
    from clients_cpp.source as named_lvalue_parameterized_roundtrip_spec with (
      \post emp
    ).
  
  

Lemma named_lvalue_parameterized_roundtrip_proof :
  verify[clients_cpp.module] "named_lvalue_parameterized_roundtrip()".
Proof using MOD.
  rewrite /optional_uint8_value_lvalue_ctor_spec
    /optional_uint8_has_value_spec
    /optional_uint8_deref_const_lvalue_spec
    /optional_uint8_destructor_spec
    /assert_fail_unreachable_spec
    /check_named_lvalue_roundtrip_helper_spec.
  verify_spec; go.
  Unshelve.
  all: ego; go.

Unshelve.
exact 37%Z.
Qed.

End with_cpp.
