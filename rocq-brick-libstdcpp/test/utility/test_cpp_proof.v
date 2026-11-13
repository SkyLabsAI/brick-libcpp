Require Import skylabs.auto.cpp.prelude.proof.

Require Import skylabs.brick.libstdcpp.utility.spec.

Require Import skylabs.brick.libstdcpp.test.utility.test_cpp.

#[local] Set Warnings "+sl-transparent-constants".

mlock
Definition fooR `{Σ : cpp_logic, σ : genv} q := structR "foo" q.
#[only(type_ptr,cfracsplittable,lazy_unfold)] derive fooR.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "test_move()" as test_move from source with (
    \post emp).

  cpp.spec "foo::foo()" as foo_ctor from source with (
    \this this
    \post this |-> fooR 1$m).

  cpp.spec "foo::~foo()" as foo_dtor from source with (
    \this this
    \pre this |-> fooR 1$m
    \post emp).

  Lemma test_move_spec : verify[source] "test_move()".
  Proof. verify_spec; go. Qed.
End with_cpp.
