
Require Import
  skylabs.brick.libstdcpp.test.optional.empty_deref_max_rejected_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context
    `{MOD : !empty_deref_max_rejected_cpp.source ⊧ σ}.
  cpp.spec "__assert_fail" from empty_deref_max_rejected_cpp.source
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
    from empty_deref_max_rejected_cpp.source as nullopt_copy_ctor_spec with (
      \this this
      \with{other : ptr}
      \arg{other} "" (Vref other)
      \post this |-> structR "std::nullopt_t" 1$m
    ).

  cpp.spec "std::nullopt_t::~nullopt_t()" from empty_deref_max_rejected_cpp.source
    as nullopt_destructor_spec with (
      \this this
      \pre this |-> structR "std::nullopt_t" 1$m
      \post emp
    ).

  cpp.spec "empty_deref_max_rejected()"
    from empty_deref_max_rejected_cpp.source
    as empty_deref_max_rejected_spec with (\post emp).
#[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.
#[local] Instance optional_uint8_R_read_learn :
  AtLearnEq3 optional_uint8.R := ltac:(solve_learnable).

Lemma empty_deref_max_rejected_proof :
  denoteModule empty_deref_max_rejected_cpp.source |--
    (▷ optional_uint8_nullopt_ctor_spec **
     ▷ optional_uint8_deref_const_lvalue_spec **
     ▷ optional_uint8_destructor_spec -*
     empty_deref_max_rejected_spec).
Proof using MOD.
  rewrite /optional_uint8_nullopt_ctor_spec
    /optional_uint8_deref_const_lvalue_spec
    /optional_uint8_destructor_spec.
rewrite /assert_fail_unreachable_spec /nullopt_copy_ctor_spec /nullopt_destructor_spec.

  verify_spec; go.
  Unshelve.
  all: try exact None.
  all: ego; go.

all: try (
  iApply wp_init_constructor_inline;
    [exact (InlineMe _) | go |]
).
all: go.
all: try (
  iApply destroy_val_named_inline;
    [exact (InlineMe _) | go |]
).
all: go.
Unshelve.
all: try exact (Vint 255).
all: try exact (1$c)%cQp.
all: ego; go.
all: try (
  rewrite !optional_uint8.R.unlock !_at_sep !_at_pureR;
  wname [ (o_addr |-> optional_uint8.spineR _ None) ] "Hempty";
  wname [ (o_addr |-> optional_uint8.spineR _ (Some _)) ] "Hengaged";
  iDestruct (observe_2 [| (None : option ptr) = Some _ |]
    with "Hempty Hengaged") as %Hbad;
  discriminate Hbad
).

Unshelve.
all: try exact (Vint 255).
all: try exact (1$c)%cQp.
all: try (ego; go).
Fail Qed.
Abort.

  
End with_cpp.
