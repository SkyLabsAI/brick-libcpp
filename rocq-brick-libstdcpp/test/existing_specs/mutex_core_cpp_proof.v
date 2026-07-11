
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.mutex_core_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec "mutex_construct_destroy()" as mutex_construct_destroy_spec from source with (
    \post emp).

  Lemma mutex_construct_destroy_ok :
    verify[source] "mutex_construct_destroy()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
  Qed.

  Require Import skylabs.brick.libstdcpp.cassert.spec.

  cpp.spec "mutex_direct_lock_unlock()" as mutex_direct_lock_unlock_spec from source with (
    \post[Vint 1] emp).

  Lemma mutex_direct_lock_unlock_ok :
    verify[source] "mutex_direct_lock_unlock()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
  Qed.

  cpp.spec "mutex_basic_lockable_lock_unlock()" as mutex_basic_lockable_lock_unlock_spec from source with (
    \post[Vint 2] emp).

  Lemma mutex_basic_lockable_lock_unlock_ok :
    verify[source] "mutex_basic_lockable_lock_unlock()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
  Qed.

  cpp.spec "mutex_direct_try_lock()" as mutex_direct_try_lock_spec from source with (
    \post{b}[Vbool b] emp).

  Lemma mutex_direct_try_lock_ok :
    verify[source] "mutex_direct_try_lock()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.

wp_if; go $usenamed=true.

Qed.

  cpp.spec "mutex_lockable_try_lock()" as mutex_lockable_try_lock_spec from source with (
    \post{b}[Vbool b] emp).

  Lemma mutex_lockable_try_lock_ok :
    verify[source] "mutex_lockable_try_lock()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
    wp_if; go $usenamed=true.
  Qed.

  cpp.spec "mutex_realistic_composition()" as mutex_realistic_composition_spec from source with (
    \post{r}[Vint r] [| r = 1 \/ r = 2 |]).

  Lemma mutex_realistic_composition_ok :
    verify[source] "mutex_realistic_composition()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
    wp_if; go $usenamed=true.

all: iPureIntro; lia.

Qed.

  Lemma lock_direct_and_basiclockable_equivalent :
    mutex.lock_spec -|- mutex.lock_spec_alt.
  Proof. exact mutex.lock_spec_entails_lock_spec_alt. Qed.

  Lemma unlock_direct_and_basiclockable_equivalent :
    mutex.unlock_spec -|- mutex.unlock_spec_alt.
  Proof. exact mutex.unlock_spec_entails_unlock_spec_alt. Qed.

  Lemma try_lock_direct_and_lockable_equivalent :
    mutex.try_lock_spec -|- mutex.try_lock_spec_alt.
  Proof. exact mutex.try_lock_spec_entails_try_lock_spec_alt. Qed.

  Lemma recursive_acquisition_locked_state_unreachable g thr q :
    mutex.locked g thr q ** mutex.locked g thr q |-- False.
  Proof.
    go $usenamed=true.

work $usenamed=true.

iDestruct (observe_2_uncurry_elim False (mutex.locked g thr q) (mutex.locked g thr q) with "[$]") as "(_ & Hfalse)". done.

Qed.

  Lemma wrong_thread_unlock_precondition_unreachable owner caller :
    owner <> caller ->
    current_thread owner ** current_thread caller |-- False.
  Proof.
    intros Hneq.
    iIntros "[Howner Hcaller]".
    iDestruct (observe_2_uncurry_elim [| owner = caller |]
      (current_thread owner) (current_thread caller)
      with "[$Howner $Hcaller]") as "(_ & %Heq)".
    contradiction.
  Qed.

  #[local] Instance token_frac_splittable g :
    FracSplittable_0 (mutex.token g).
  Proof. constructor; typeclasses eauto. Qed.

  Lemma duplicate_full_unlocked_authority_unreachable g :
    mutex.token g 1 ** mutex.token g 1 |-- False.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (observe_2_uncurry_elim [| (1 + 1 <= 1)%Qp |]
      (mutex.token g 1) (mutex.token g 1)
      (O := frac_splittable_0_frac_valid_2 (mutex.token g) 1 1)
      with "[$H1 $H2]") as "(_ & %Hbad)".
    vm_compute in Hbad.

iPureIntro. apply Hbad. reflexivity.

Qed.

End with_cpp.
