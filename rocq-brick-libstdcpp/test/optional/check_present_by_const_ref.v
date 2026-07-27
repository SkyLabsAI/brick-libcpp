
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
  
Lemma check_present_by_const_ref_proof :
    verify[clients_cpp.module]
      "check_present_by_const_ref(const std::optional<unsigned char>&)".

  Proof using MOD.
    rewrite /optional_uint8_has_value_spec
      /optional_uint8_deref_const_lvalue_spec.
    verify_spec.
    
repeat first [ progress (go $usenamed=true) | iExists _; iFrame ].

rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ q (Some 5%Z) (Some p))).

go $usenamed=true.

go $usenamed=true.

  Qed.
End with_cpp.
