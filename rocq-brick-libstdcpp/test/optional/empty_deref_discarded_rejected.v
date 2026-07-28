
Require Import
  skylabs.brick.libstdcpp.test.optional.empty_deref_discarded_rejected_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.optional.hints.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context
    `{MOD : !empty_deref_discarded_rejected_cpp.source ⊧ σ}.
  cpp.spec "std::nullopt_t::nullopt_t(const std::nullopt_t&)"
    from empty_deref_discarded_rejected_cpp.source as nullopt_copy_ctor_spec with (
      \this this
      \with{other : ptr}
      \arg{other} "" (Vref other)
      \post this |-> structR "std::nullopt_t" 1$m
    ).

  cpp.spec "std::nullopt_t::~nullopt_t()" from empty_deref_discarded_rejected_cpp.source
    as nullopt_destructor_spec with (
      \this this
      \pre this |-> structR "std::nullopt_t" 1$m
      \post emp
    ).

  cpp.spec "empty_deref_discarded_rejected()"
    from empty_deref_discarded_rejected_cpp.source
    as empty_deref_discarded_rejected_spec with (\post emp).

Lemma empty_deref_discarded_rejected_proof :
  denoteModule empty_deref_discarded_rejected_cpp.source |--
    (▷ optional_uint8_nullopt_ctor_spec **
     ▷ optional_uint8_deref_const_lvalue_spec **
     ▷ optional_uint8_destructor_spec -*
     empty_deref_discarded_rejected_spec).
Proof using MOD.
  rewrite /optional_uint8_nullopt_ctor_spec
    /optional_uint8_deref_const_lvalue_spec
    /optional_uint8_destructor_spec.
rewrite /nullopt_copy_ctor_spec /nullopt_destructor_spec.

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
all: try exact (Vint 0).
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
all: try exact (Vint 0).
all: try exact (1$c)%cQp.
all: try (ego; go).

all: try exact 0%Z.

all: try exact o_addr.

all: try solve [ ework ].

all: try exact None.

all: try solve [ ework ].
Fail Qed.
Abort.

  

End with_cpp.
