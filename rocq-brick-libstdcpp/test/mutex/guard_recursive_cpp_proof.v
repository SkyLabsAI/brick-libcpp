Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.guard_recursive_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec "test_one_answer()" from source with (
    \post[Vint 42] emp
  ).
  cpp.spec "test_other_answer()" from source with (
    \post[Vint 42] emp
  ).

  Lemma test_one_answer_ok :
    verify?[source] "test_one_answer()".
  Proof.
    verify_spec; go.
  Admitted.

  Lemma test_other_answer_ok :
    verify?[source] "test_other_answer()".
  Proof.
    verify_spec; go.
  Admitted.

  (* WIP, feel free to discard. *)
  (*
  cpp.spec "C::other_answer()" from source with (
    \this this
    (* \pre *)
    \pre{K} do_lock c g K
    \post K
  ).
  *)

End with_cpp.
