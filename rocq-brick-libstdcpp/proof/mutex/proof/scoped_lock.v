Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.scoped_lock.
Require Import skylabs.brick.libstdcpp.mutex.spec.unique_lock.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  Import scoped_lock.

  cpp.spec "std::tie<...<std::mutex, std::mutex>>(std::mutex&, std::mutex&)" from source inline.
  cpp.spec "std::tuple<...<std::mutex&, std::mutex&>>::tuple<1b, 1b>(std::mutex&, std::mutex&)" from source inline.
  cpp.spec "std::lock<std::mutex, std::mutex, ...<>>(std::mutex&, std::mutex&)" from source inline.

  Lemma ctor_ok : verify?[source] ctor_spec.
  Proof.
    verify_spec; go.
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

