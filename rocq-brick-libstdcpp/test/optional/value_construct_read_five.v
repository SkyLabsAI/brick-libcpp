
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


  


  
  
  #[global] Instance optional_uint8_value_rvalue_ctor_client_spec_instance :
    SpecFor clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)" :=
    SpecFor.mk clients_cpp.module
      "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)"
      optional_uint8_value_rvalue_ctor_spec.

cpp.spec "value_construct_read_five()" from clients_cpp.source
    as value_construct_read_five_spec with (
      \post emp
    ).
  
  
  
  
Lemma optional_uint8_R_engaged_byte
    (o p : ptr) (q : cQp.t) (b : Z) :
  o |-> optional_uint8.R q (Some b) (Some p) |--
    p |-> ucharR q b ** True.
Proof.
  rewrite optional_uint8.R.unlock !_at_sep !_at_pureR.
  go.
Qed.

#[local] Hint Resolve
  fractional.UNSAFE_read_prim_learn : sl_opacity.
#[local] Instance optional_uint8_R_read_learn :
  AtLearnEq3 optional_uint8.R := ltac:(solve_learnable).

Lemma value_construct_read_five_proof :
  verify[clients_cpp.module] "value_construct_read_five()".
Proof using MOD.
  rewrite /optional_uint8_value_rvalue_ctor_spec
    /optional_uint8_has_value_spec
    /optional_uint8_deref_const_lvalue_spec
    /optional_uint8_destructor_spec
    /assert_fail_unreachable_spec.
  verify_spec; go.
  Unshelve.
  ego.
  - wapply (optional_uint8_R_engaged_byte o_addr t 1$c 5); go.
  - go.
Qed.
End with_cpp.


