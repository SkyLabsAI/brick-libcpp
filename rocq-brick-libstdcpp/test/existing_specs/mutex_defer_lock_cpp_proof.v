
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.mutex_defer_lock_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  Require Import skylabs.brick.libstdcpp.cassert.spec.

  cpp.spec "test_copy_lifecycle()" as test_copy_lifecycle_spec from source with (
    \prepost{q} _global "std::defer_lock" |-> defer_lock_t.R q
    \post emp
  ).

  Theorem test_copy_lifecycle_ok : verify[source] "test_copy_lifecycle()".
  Proof.
    verify_spec.

    go $usenamed=true.

  Qed.

  cpp.spec "test_source_survives_inner_copy()" as test_source_survives_inner_copy_spec from source with (
    \prepost{q} _global "std::defer_lock" |-> defer_lock_t.R q
    \post emp
  ).

  Theorem test_source_survives_inner_copy_ok :
    verify[source] "test_source_survives_inner_copy()".
  Proof.
    verify_spec.

    go $usenamed=true.

  Qed.

  cpp.spec "test_unique_lock_with_copied_defer_tag()" as test_unique_lock_with_copied_defer_tag_spec from source with (
    \prepost{q} _global "std::defer_lock" |-> defer_lock_t.R q
    \post emp
  ).

  Theorem test_unique_lock_with_copied_defer_tag_ok :
    std.cassert.specs |--
    verify[source] "test_unique_lock_with_copied_defer_tag()".
  Proof.
    rewrite /std.cassert.specs.

    verify_spec.

    go $usenamed=true.

    iExists emp.
    go $usenamed=true.

  Qed.

  cpp.spec "main()" as main_spec from source with (
    \prepost{q} _global "std::defer_lock" |-> defer_lock_t.R q
    \post[Vint 0] emp
  ).

  Theorem main_ok : verify[source] "main()".
  Proof.
    verify_spec.

    go $usenamed=true.

  Qed.

  (* A destructor consumes full mutable ownership.  No positive live fraction
     can coexist at the same address for a second destructor or later copy. *)
  Theorem defer_lock_consumed_lifecycle_unreachable
      (p : ptr) (q : cQp.t) :
    p |-> defer_lock_t.R 1$m **
    p |-> defer_lock_t.R q |-- False.
  Proof.

    go $usenamed=true.

  Qed.
End with_cpp.
