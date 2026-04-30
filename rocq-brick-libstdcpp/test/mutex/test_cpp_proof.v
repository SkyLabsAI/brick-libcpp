Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {HAS_THREADS : HasStdThreads Σ}.
  Context `{MOD : test_cpp.source ⊧ σ}. (* σ is the whole program *)

  cpp.spec "test_mutex()" as test_mutex_spec with
      (\post emp).

  Theorem test_mutex_ok : verify[source] "test_mutex()".
  Proof using HAS_THREADS.
    verify_spec; go.
    iExists emp; go.
  Qed.

  cpp.spec "test_scoped_lock()" as test_scoped_lock_spec from source with
  (
    \persist{thr} current_thread thr
    \post emp
  ).

  Lemma test_scoped_lock_ok : verify[source] "test_scoped_lock()".
  Proof.
    verify_spec; go.
    iExists emp; go.
    iExists emp; go.
  Qed.
End with_cpp.
