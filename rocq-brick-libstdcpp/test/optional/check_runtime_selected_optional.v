
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


  cpp.spec "check_runtime_selected_optional(bool)"
    from clients_cpp.source as check_runtime_selected_optional_spec with (
      \with{choose_present : bool}
      \arg{choose_present} "choose_present" (Vbool choose_present)
      \post emp
    ).
  
  Lemma check_runtime_selected_optional_proof :
    verify[clients_cpp.module] "check_runtime_selected_optional(bool)".
    try rewrite /optional_uint8_nullopt_ctor_template_spec.
    try rewrite /optional_uint8_has_value_template_spec.
    try rewrite /optional_uint8_deref_const_lvalue_template_spec.
    try rewrite /optional_uint8_destructor_template_spec.
    try rewrite /assert_fail_unreachable_spec.
    try rewrite /nullopt_copy_ctor_spec.
    try rewrite /nullopt_destructor_spec.

  Proof using MOD.
    rewrite /optional_uint8_nullopt_ctor_spec
      /optional_uint8_value_rvalue_ctor_spec
      /optional_uint8_has_value_spec
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



all: repeat first [ progress (go) | iExists _; iFrame | rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ _ _ _)) | (iApply wp_init_constructor_inline; [exact (InlineMe _) | go |]) | (iApply destroy_val_named_inline; [exact (InlineMe _) | go |]) ].

wp_if.

all: repeat first [ progress (go) | iExists _; iFrame | rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ _ _ _)) | (iApply wp_init_constructor_inline; [exact (InlineMe _) | go |]) | (iApply destroy_val_named_inline; [exact (InlineMe _) | go |]) ].

all: rewrite (AutoUnlocking.unfold_eq (Unfoldable := optional_uint8.R_unfoldable _ _ _ _ 1$m (Some 5%Z) (Some t))).

all: go.

iExists (Some 5%Z), (Some t). go.

Unshelve.

exact t.

Qed. End with_cpp.
