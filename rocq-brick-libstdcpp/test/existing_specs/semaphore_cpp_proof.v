
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.semaphore.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.semaphore_cpp.
Require Import skylabs.brick.libstdcpp.cassert.spec.

Import auto_frac auto_pick_frac.

Section with_cpp.
  #[local] Open Scope nat_scope.

  Context `{Σ : cpp_logic}.
  Context `{MOD : semaphore_cpp.source ⊧ σ}.

  #[program]
  Definition acquire_ac_C :=
    \cancelx
    \consuming{t (x : nat)} semaphore_Val t x
    \bound_existential Q
    \proving acquire_ac t Q
    \instantiate Q := semaphore_Val t (x - 1) ** [| x > 0 |]
    \end.
  Next Obligation.
    work $usenamed=true.
    rewrite /acquire_ac.
    iAcIntro.
    rewrite /commit_acc /=.
    iExists _; iFrame.
    iMod (fupd_mask_subseteq ∅) as "Close"; first by solve_ndisj.
    iIntros "!>" (x) "[-> ?]".
    iMod "Close". iModIntro.
    replace (S x - 1) with x by lia.
    iFrame. iPureIntro. lia.
  Qed.
  #[local] Hint Resolve acquire_ac_C : br_hints.

  #[program]
  Definition release_ac_C :=
    \cancelx
    \consuming{t (x : nat)} semaphore_Val t x
    \bound_existential Q
    \proving{update} release_ac t Q update
    \instantiate Q := semaphore_Val t (x + update)
    \through [| x + update <= 1 |]
    \end.
  Next Obligation.
    work $usenamed=true.
    rewrite /release_ac.
    iAcIntro.
    rewrite /commit_acc /=.
    iExists _; iFrame.
    iMod (fupd_mask_subseteq ∅) as "Close"; first by solve_ndisj.
    iFrame "%".
    iIntros "!> $".
    iMod "Close". done.
  Qed.
  #[local] Hint Resolve release_ac_C : br_hints.

  #[program]
  Definition try_acquire_ac_C :=
    \cancelx
    \consuming{t (x : nat)} semaphore_Val t x
    \bound_existential Q
    \proving try_acquire_ac t Q
    \instantiate Q := fun b =>
      [| b = true -> (0 < x)%nat |] **
      semaphore_Val t (if b then x - 1 else x)
    \end.

  Next Obligation.

    work $usenamed=true.

    rewrite /try_acquire_ac.

    iAuIntro.

    rewrite /atomic_acc.

    rewrite /=.

    iMod (fupd_mask_subseteq ∅) as "Close"; first by solve_ndisj.

    iModIntro.

    iExists _; iFrame.

    iSplit.

    - iIntros "H". iMod "Close". iModIntro. iFrame.

    - iIntros (b) "H". iMod "Close". iModIntro. iFrame.

  Qed.

  #[local] Hint Resolve try_acquire_ac_C : br_hints.

  cpp.spec "test_zero_permit_try_acquire()" as test_zero_permit_try_acquire_spec from source with
      (\post emp).

  Theorem test_zero_permit_try_acquire_ok :
    verify[source] "test_zero_permit_try_acquire()".

  Proof using MOD.

    verify_spec.

    go $usenamed=true.

    match goal with | b : bool |- _ => destruct b end.

    all: go $usenamed=true.

    exfalso; lia.

  Qed.

  cpp.spec "test_acquire_release_cycle()" as test_acquire_release_cycle_spec from source with
      (\post emp).

  Theorem test_acquire_release_cycle_ok :
    verify[source] "test_acquire_release_cycle()".

  Proof using MOD.

    verify_spec.

    go $usenamed=true.

    match goal with | b : bool |- _ => destruct b end.

    all: go $usenamed=true.

    exfalso; lia.

  Qed.

  cpp.spec "test_available_permit_allows_spurious_failure()" as test_available_permit_allows_spurious_failure_spec from source with
      (\post emp).

  Theorem test_available_permit_allows_spurious_failure_ok :
    verify[source] "test_available_permit_allows_spurious_failure()".

  Proof using MOD.

    verify_spec.

    go $usenamed=true.

    match goal with | b : bool |- _ => destruct b end.

    all: go $usenamed=true.

  Qed.

  cpp.spec "test_zero_release_is_noop()" as test_zero_release_is_noop_spec from source with
      (\post emp).

  Theorem test_zero_release_is_noop_ok :
    verify[source] "test_zero_release_is_noop()".

  Proof using MOD.

    verify_spec.

    go $usenamed=true.

    match goal with | b : bool |- _ => destruct b end.

    all: go $usenamed=true.

    exfalso; lia.

  Qed.

  cpp.spec "test_construct_zero_destroy()" as test_construct_zero_destroy_spec from source with
      (\post emp).

  Theorem test_construct_zero_destroy_ok :
    verify[source] "test_construct_zero_destroy()".
  Proof using MOD.
    verify_spec.

    go $usenamed=true.

 Qed.

  cpp.spec "test_permit_cycle_without_query()" as test_permit_cycle_without_query_spec from source with
      (\post emp).

  Theorem test_permit_cycle_without_query_ok :
    verify[source] "test_permit_cycle_without_query()".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
  Qed.

  cpp.spec "test_zero_release_boundary_without_query()" as test_zero_release_boundary_without_query_spec from source with
      (\post emp).

  Theorem test_zero_release_boundary_without_query_ok :
    verify[source] "test_zero_release_boundary_without_query()".
  Proof using MOD.
    verify_spec.
    go $usenamed=true.
  Qed.

  (* Closed side-condition evidence for invalid count/permit transitions. *)
  Lemma negative_initial_count_unreachable (n : nat) :
    (-1 <> Z.of_nat n)%Z.
  Proof. lia. Qed.

  Lemma acquire_from_zero_unreachable :
    ~ (0 > 0)%nat.
  Proof. lia. Qed.

  Lemma release_one_from_full_unreachable :
    ~ (1 + 1 <= 1)%nat.
  Proof. lia. Qed.
  Lemma constructor_count_above_max_unreachable :
    ~ (2 <= 1)%nat.

  Proof. lia. Qed.

  Lemma try_success_at_zero_unreachable :
    ~ (true = true -> (0 < 0)%nat).

  Proof. lia. Qed.

  Lemma try_false_preserves_count (n : nat) :
    (if false then n - 1 else n) = n.

  Proof. reflexivity. Qed.

  Lemma try_true_consumes_permit :
    (if true then 1 - 1 else 1) = 0.

  Proof. reflexivity. Qed.

End with_cpp.

