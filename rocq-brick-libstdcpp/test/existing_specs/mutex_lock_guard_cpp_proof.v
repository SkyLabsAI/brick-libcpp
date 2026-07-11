
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.mutex_lock_guard_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec "lock_guard_scope_round_trip()" as lock_guard_scope_round_trip_spec from source with (
    \post[Vint 42] emp).

  Lemma lock_guard_scope_round_trip_ok : verify[source] "lock_guard_scope_round_trip()".
  Proof.

    verify_spec; go $usenamed=true.

    iExists emp; go $usenamed=true.
  Qed.

  cpp.spec "lock_guard_reacquire_after_scope()" as lock_guard_reacquire_after_scope_spec from source with (
    \post[Vint 9] emp).

  Lemma lock_guard_reacquire_after_scope_ok : verify[source] "lock_guard_reacquire_after_scope()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
  Qed.

  cpp.spec "lock_guard_function_scope_cleanup()" as lock_guard_function_scope_cleanup_spec from source with (
    \post[Vint 11] emp).

  Lemma lock_guard_function_scope_cleanup_ok : verify[source] "lock_guard_function_scope_cleanup()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists emp; go $usenamed=true.
  Qed.

  cpp.spec "main()" as main_spec from source with (\post[Vint 0] emp).

  Lemma main_ok : verify[source] "main()".
  Proof.
    verify_spec; go $usenamed=true.

  Qed.

  Lemma second_live_lock_capability_unreachable
      (g : gname) (thr : thread_idT) (q : Qp) :
    mutex.locked g thr q ** mutex.locked g thr q |-- False.
  Proof.
    go $usenamed=true.

    iDestruct (token_excl with "[$]") as %[].

    Unshelve. done.

    Restart.

    iIntros "[Hlocked1 Hlocked2]".

    iPoseProof (token_excl (P := mutex.locked g thr q) with "Hlocked1") as "Hexcl".

    iDestruct ("Hexcl" with "Hlocked2") as %[].

  Qed.

  (** Satisfying an external unlock while preserving the guard destructor's
      capability would require two copies of the exclusive lock capability. *)
  Lemma manual_unlock_while_guard_remains_destructible_unreachable
      (this mp : ptr) (g : gname) (thr : thread_idT) (q : Qp) (P : mpred) :
    this |-> lock_guard.R (mp, g, q) 1$m P **
    mutex.locked g thr q ** ▷ P **
    mutex.locked g thr q ** ▷ P |-- False.
  Proof.
    iIntros "[Hguard [Hlocked1 [HP1 [Hlocked2 HP2]]]]".

    iPoseProof (second_live_lock_capability_unreachable g thr q
      with "[$Hlocked1 $Hlocked2]") as "Hfalse".

    iDestruct "Hfalse" as %[].

  Qed.

  (** Two successful locking constructors over the same non-recursive mutex
      cannot both leave live guard states for the same thread and capability. *)
  Lemma two_live_guard_success_states_unreachable
      (this1 this2 mp : ptr) (g : gname) (thr : thread_idT)
      (q : Qp) (P : mpred) :
    (this1 |-> lock_guard.R (mp, g, q) 1$m P **
      P ** mutex.locked g thr q) **
    (this2 |-> lock_guard.R (mp, g, q) 1$m P **
      P ** mutex.locked g thr q) |-- False.
  Proof.
    iIntros "[[Hguard1 [HP1 Hlocked1]] [Hguard2 [HP2 Hlocked2]]]".
    iPoseProof (second_live_lock_capability_unreachable g thr q
      with "[$Hlocked1 $Hlocked2]") as "Hfalse".
    iDestruct "Hfalse" as %[].
  Qed.

  (** Calling the destructor twice would require two complete copies of its
      consuming precondition, including the exclusive lock capability. *)
  Lemma two_destructor_preconditions_unreachable
      (this mp : ptr) (g : gname) (thr : thread_idT)
      (q : Qp) (P : mpred) :
    (this |-> lock_guard.R (mp, g, q) 1$m P **
      mutex.locked g thr q ** ▷ P) **
    (this |-> lock_guard.R (mp, g, q) 1$m P **
      mutex.locked g thr q ** ▷ P) |-- False.
  Proof.
    iIntros "[[Hguard1 [Hlocked1 HP1]] [Hguard2 [Hlocked2 HP2]]]".
    iPoseProof (second_live_lock_capability_unreachable g thr q
      with "[$Hlocked1 $Hlocked2]") as "Hfalse".
    iDestruct "Hfalse" as %[].
  Qed.

  (** Preserving a live full guard while separately satisfying the mutex
      destructor's full object-ownership premise duplicates the guarded mutex
      representation. This rules out destroying the referenced/owned mutex
      before the guard. *)
  Lemma live_guard_and_mutex_destruction_ownership_unreachable
      (this mp : ptr) (g : gname) (P : mpred) :
    this |-> lock_guard.R (mp, g, (1 : Qp)) 1$m P **
    mp |-> mutex.R g 1$m P |-- False.
  Proof.
    rewrite lock_guard.R.unlock.

    go $usenamed=true.

  Qed.

End with_cpp.
