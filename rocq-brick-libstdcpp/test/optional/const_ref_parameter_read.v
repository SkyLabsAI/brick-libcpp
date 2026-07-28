
Require Import skylabs.brick.libstdcpp.test.optional.clients_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.optional.hints.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : !clients_cpp.source ⊧ σ}.
  cpp.spec "std::nullopt_t::nullopt_t(const std::nullopt_t&)"
    from clients_cpp.source as nullopt_copy_ctor_spec with (
      \this this
      \with{other : ptr}
      \arg{other} "" (Vref other)
      \post this |-> structR "std::nullopt_t" 1$m
    ).

  cpp.spec "std::nullopt_t::~nullopt_t()" from clients_cpp.source
    as nullopt_destructor_spec with (
      \this this
      \pre this |-> structR "std::nullopt_t" 1$m
      \post emp
    ).

  
  #[global] Instance optional_uint8_value_rvalue_ctor_client_spec_instance :
    SpecFor clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)" :=
    SpecFor.mk clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)"
      optional_uint8_value_rvalue_ctor_spec.


  cpp.spec "check_present_by_const_ref(const std::optional<unsigned char>&)"
    from clients_cpp.source as check_present_by_const_ref_helper_spec with (
      \arg{o} "o" (Vref o)
      \prepost{q p} o |-> optional_uint8.R q (Some 5%Z) (Some p)
      \post emp
    ).

  cpp.spec "check_empty_by_const_ref(const std::optional<unsigned char>&)"
    from clients_cpp.source as check_empty_by_const_ref_helper_spec with (
      \arg{o} "o" (Vref o)
      \prepost{q} o |-> optional_uint8.R q None None
      \post emp
    ).

  cpp.spec "const_ref_parameter_read()" from clients_cpp.source
    as const_ref_parameter_read_spec with (\post emp).
  
  


Lemma const_ref_parameter_read_proof :
  verify[clients_cpp.module] "const_ref_parameter_read()".
Proof using MOD.
  rewrite /optional_uint8_nullopt_ctor_spec
    /optional_uint8_value_rvalue_ctor_spec
    /optional_uint8_has_value_spec
    /optional_uint8_deref_const_lvalue_spec
    /optional_uint8_destructor_spec
    /nullopt_copy_ctor_spec
    /nullopt_destructor_spec
    /check_present_by_const_ref_helper_spec
    /check_empty_by_const_ref_helper_spec.
  verify_spec; go.
  Unshelve.
  all: ego; go.
  Unshelve.
  exact t.
Qed.

End with_cpp.
