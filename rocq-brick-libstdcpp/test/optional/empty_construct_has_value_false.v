
Require Import skylabs.brick.libstdcpp.test.optional.clients_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : !clients_cpp.source ⊧ σ}.

  cpp.spec "empty_construct_has_value_false()" from clients_cpp.source
    as empty_construct_has_value_false_spec with (
      \post emp
    ).
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

  Lemma empty_construct_has_value_false_proof :
    verify[clients_cpp.module] "empty_construct_has_value_false()".
  Proof using MOD.
    rewrite /optional_uint8_nullopt_ctor_spec
      /optional_uint8_has_value_spec
      /optional_uint8_destructor_spec
      /assert_fail_unreachable_spec
      /nullopt_copy_ctor_spec
      /nullopt_destructor_spec.
    verify_spec.

    (* Goal-shape-conditional instead of positional: each alternative only
       fires on the shape it targets (existential / bare wand / a resource
       stranded beside `wp_block`), so it doesn't matter exactly where a
       given `go` version stops. The bare [iFrame] is what re-absorbs a
       resource automation left dangling next to `▷ wp_block ...`, which is
       what lets the next `go` continue instead of getting stuck. *)
    repeat first
      [ progress go
      | iExists _; iFrame
      | iIntros "?"
      | iFrame ].

    Unshelve.
    all: try exact p.
    all: try done.
  Qed.
End with_cpp.

