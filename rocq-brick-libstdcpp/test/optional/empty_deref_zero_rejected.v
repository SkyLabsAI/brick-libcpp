
Require Import
  skylabs.brick.libstdcpp.test.optional.empty_deref_zero_rejected_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context
    `{MOD : !empty_deref_zero_rejected_cpp.source ⊧ σ}.
  cpp.spec "__assert_fail" from empty_deref_zero_rejected_cpp.source
    as assert_fail_unreachable_spec with (
      \with{assertion file function_name : ptr} {line : Z}
      \arg{assertion} "__assertion" (Vptr assertion)
      \arg{file} "__file" (Vptr file)
      \arg{line} "__line" (Vint line)
      \arg{function_name} "__function" (Vptr function_name)
      \pre [| False |]
      \post emp
    ).

  cpp.spec "std::nullopt_t::nullopt_t(const std::nullopt_t&)"
    from empty_deref_zero_rejected_cpp.source as nullopt_copy_ctor_spec with (
      \this this
      \with{other : ptr}
      \arg{other} "" (Vref other)
      \post this |-> structR "std::nullopt_t" 1$m
    ).

  cpp.spec "std::nullopt_t::~nullopt_t()" from empty_deref_zero_rejected_cpp.source
    as nullopt_destructor_spec with (
      \this this
      \pre this |-> structR "std::nullopt_t" 1$m
      \post emp
    ).

  cpp.spec "empty_deref_zero_rejected()"
    from empty_deref_zero_rejected_cpp.source
    as empty_deref_zero_rejected_spec with (\post emp).
  Lemma empty_deref_zero_rejected_proof :
    denoteModule empty_deref_zero_rejected_cpp.source |--
      (▷ optional_uint8_nullopt_ctor_spec **
       ▷ optional_uint8_deref_const_lvalue_spec **
       ▷ optional_uint8_destructor_spec -*
       empty_deref_zero_rejected_spec).
  Proof using MOD.
    rewrite /optional_uint8_nullopt_ctor_spec
      /optional_uint8_deref_const_lvalue_spec
      /optional_uint8_destructor_spec.
    verify_spec.
    


repeat first
      [ progress (go)
      | iExists _; iFrame
      | rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ _ _ _))
      | (iApply wp_init_constructor_inline;
          [exact (InlineMe _) | go |])
      | (iApply destroy_val_named_inline;
          [exact (InlineMe _) | go |])
      ].

Unshelve. all: try exact None.
repeat first
      [ progress (go)
      | iExists _; iFrame
      | rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ _ _ _))
      | (iApply wp_init_constructor_inline;
          [exact (InlineMe _) | go |])
      | (iApply destroy_val_named_inline;
          [exact (InlineMe _) | go |])
      ].
Fail Qed.
Abort.

End with_cpp.
