Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.lock_guard.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  Import lock_guard.

  Lemma ctor_ok : verify[source] ctor_spec.
  Proof.
    verify_spec.
    go; try by ego.
    iExists _; go.
    by rewrite left_id_L.
  Qed.

  Lemma dtor_ok : verify[source] dtor_spec.
  Proof.
    verify_spec.
    rewrite !R.unlock.
    go; try by ego.
    iExists _; go.
    rewrite !left_id_L.
    go.
  Qed.

End with_cpp.
