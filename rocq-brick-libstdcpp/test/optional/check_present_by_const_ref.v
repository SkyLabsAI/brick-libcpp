
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

  cpp.spec
    "check_present_by_const_ref(const std::optional<unsigned char>&)"
    from clients_cpp.source as check_present_by_const_ref_spec with (
      \arg{o} "o" (Vref o)
      \prepost{q p} o |-> optional_uint8.R q (Some 5%Z) (Some p)
      \post emp
    ).
  

#[program] Definition optional_uint8_R_engaged_byte_C
    (o p : ptr) (q : cQp.t) (b : Z) :=
  \cancelx
  \consuming o |-> optional_uint8.R q (Some b) (Some p)
  \proving p |-> ucharR q b
  \end.
Next Obligation.
  intros.
  rewrite optional_uint8.R.unlock.
  rewrite _at_sep _at_pureR.
  go.
Qed.
#[local] Hint Resolve optional_uint8_R_engaged_byte_C : br_hints.

Lemma check_present_by_const_ref_proof :
  verify[clients_cpp.module]
    "check_present_by_const_ref(const std::optional<unsigned char>&)".
Proof using MOD.
  rewrite /optional_uint8_has_value_spec
    /optional_uint8_deref_const_lvalue_spec.
  verify_spec; go.
  Unshelve.
  all: ego; go.
Qed.

End with_cpp.
