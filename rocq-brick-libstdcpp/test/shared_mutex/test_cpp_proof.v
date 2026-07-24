Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.
Require Import skylabs.brick.libstdcpp.shared_mutex.shared_mutex. (* XXX *)
Require Import skylabs.brick.libstdcpp.test.shared_mutex.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{LOCKED : !shared_mutex.lockedG Σ}.

  (* TODO: hacky spec *)
  cpp.spec "test_shared_mutex()" as test_mutex_spec from source with (
    (* should be unnecessary *)
    \persist{thr} current_thread thr
    \post emp).

  Lemma test_mutex_ok :
    verify[source] "test_shared_mutex()".
  Proof.
    verify_spec; go.
    iExists (const emp); simpl.
    iSplit; first work.
    iIntros "[% [? H]]".
    iMod (lock_ghost.login thr _ empty with "H") as "[??]"; first set_solver.
    progress unfold not_locked.
    wuntil Kfree go.
    rewrite /Kfree/=.
    iMod (lock_ghost.logout thr _ empty with "[$]") as "?"; first set_solver.
    go.
  Qed.

  (* TODO prove the rest of the tests *)
End with_cpp.
