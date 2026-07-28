
Require Import
  skylabs.brick.libstdcpp.test.optional.lvalue_source_alias_rejected_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.optional.hints.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context
    `{MOD : !lvalue_source_alias_rejected_cpp.source ⊧ σ}.
  cpp.spec "__assert_fail" from lvalue_source_alias_rejected_cpp.source
    as assert_fail_unreachable_spec with (
      \with{assertion file function_name : ptr} {line : Z}
      \arg{assertion} "__assertion" (Vptr assertion)
      \arg{file} "__file" (Vptr file)
      \arg{line} "__line" (Vint line)
      \arg{function_name} "__function" (Vptr function_name)
      \pre [| False |]
      \post emp
    ).

  #[local] Instance optional_uint8_value_lvalue_ctor_client_spec_instance :
    SpecFor lvalue_source_alias_rejected_cpp.module
      "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)" :=
    SpecFor.mk lvalue_source_alias_rejected_cpp.module
      "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)"
      optional_uint8_value_lvalue_ctor_spec.

  cpp.spec "lvalue_source_alias_rejected()"
    from lvalue_source_alias_rejected_cpp.source
    as lvalue_source_alias_rejected_spec with (\post emp).
  


Lemma lvalue_source_alias_rejected_proof :
  denoteModule lvalue_source_alias_rejected_cpp.source |--
    (▷ optional_uint8_value_lvalue_ctor_spec **
     ▷ optional_uint8_has_value_spec **
     ▷ optional_uint8_deref_const_lvalue_spec **
     ▷ optional_uint8_destructor_spec -*
     lvalue_source_alias_rejected_spec).
Proof using MOD.
  rewrite /optional_uint8_value_lvalue_ctor_spec
    /optional_uint8_has_value_spec
    /optional_uint8_deref_const_lvalue_spec
    /optional_uint8_destructor_spec.
  verify_spec; go.
  Unshelve.
  all: ego; go.

all: try (wname [ (source_addr |-> ucharR _x_1 _x_2) ] "Hcopy"; wname [ (source_addr |-> ucharR 1$m 91) ] "Hnew"; iDestruct (observe_2 [| _x_2 = 91%Z |] with "Hcopy Hnew") as %Hsame; case_bool_decide; go; iDestruct "Hcopy" as "?"; iDestruct "Hnew" as "?"; go).
Fail Qed.
Abort.



    
End with_cpp.
