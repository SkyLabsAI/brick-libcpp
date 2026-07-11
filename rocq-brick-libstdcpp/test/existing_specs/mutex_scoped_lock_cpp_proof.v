
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.mutex_scoped_lock_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  Require Import skylabs.brick.libstdcpp.cassert.spec.

  cpp.spec "test_two_mutex_lifecycle()" as test_two_mutex_lifecycle_spec from source with (
    \post emp).

  Lemma test_two_mutex_lifecycle_ok : verify[source] "test_two_mutex_lifecycle()".
  Proof.
    verify_spec.

    go $usenamed=true.

    iExists emp; go $usenamed=true.

    iExists emp; go $usenamed=true.

  Qed.

  Definition test_two_mutex_lifecycle_B := [LINK] test_two_mutex_lifecycle_ok.
  #[local] Hint Resolve test_two_mutex_lifecycle_B : sl_opacity.

  cpp.spec "test_reacquire_after_scope()" as test_reacquire_after_scope_spec from source with (
    \post emp).

  Lemma test_reacquire_after_scope_ok : verify[source] "test_reacquire_after_scope()".
  Proof.
    verify_spec.
    go $usenamed=true.

    iExists emp; go $usenamed=true.
    iExists emp; go $usenamed=true.
  Qed.

  Definition test_reacquire_after_scope_B := [LINK] test_reacquire_after_scope_ok.
  #[local] Hint Resolve test_reacquire_after_scope_B : sl_opacity.

  cpp.spec "main()" as main_spec from source with (
    \post[Vint 0] emp).

  Lemma main_ok : verify[source] "main()".
  Proof.
    verify_spec.

    go $usenamed=true.

  Qed.

  Lemma aliased_public_mutexes_unreachable
      (p : ptr) (g1 g2 : gname) (P1 P2 : mpred) :
    p |-> mutex.R g1 1$m P1 **
    p |-> mutex.R g2 1$m P2 |-- False.
  Proof.

    go $usenamed=true.

    work $usenamed=true using mutex.R_learnable.

  Abort.

  Lemma aliased_public_mutex_unreachable
      (p : ptr) (g : gname) (P : mpred) :
    p |-> mutex.R g 1$m P **
    p |-> mutex.R g 1$m P |-- False.
  Proof.

    go $usenamed=true.

    work $usenamed=true.

    wname [ (p |-> mutex.R g _ P) ] "Hmutex".

    iDestruct (observe [| (2$m%cQp ≤ 1)%Qp |] with "Hmutex") as %Hvalid.

    exfalso; vm_compute in Hvalid; exact (Hvalid eq_refl).

  Qed.

  Lemma already_owned_reentry_unreachable
      (g : gname) (thr : thread_idT) (q : Qp) :
    mutex.locked g thr q ** mutex.locked g thr q |-- False.
  Proof.

    go $usenamed=true.

    wname [ mutex.locked g thr q ] "Hlocked1".

    wname [ mutex.locked g thr q ] "Hlocked2".

    iCombine "Hlocked1 Hlocked2" as "Hboth".

    iDestruct (observe False with "Hboth") as "#Hfalse".

    1: apply observe_curry; apply token_excl; apply mutex.locked_exclusive.

    iExact "Hfalse".

  Qed.

  Lemma double_destruction_guard_unreachable
      (guard : ptr) (xs : list (ptr * gname * Qp * mpred)) :
    guard |-> scoped_lock.R 1$m xs **
    guard |-> scoped_lock.R 1$m xs |-- False.
  Proof.

    go $usenamed=true.

    wname [ (guard |-> scoped_lock.R _ xs) ] "Hguard".
    iDestruct (observe [| (2$m%cQp ≤ 1)%Qp |] with "Hguard") as %Hvalid.
    exfalso; vm_compute in Hvalid; exact (Hvalid eq_refl).
  Qed.

End with_cpp.
