Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.shared_mutex.shared_mutex. (* XXX *)
Require Import skylabs.brick.libstdcpp.test.shared_mutex.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!shared_mutex.lockedG Σ}.

  (* TODO: hacky spec *)
  cpp.spec "test_shared_mutex()" as test_mutex_spec from source with (
    (* should be unnecessary *)
    \persist{thr} current_thread thr
    \post emp).

  #[global] Hint Opaque shared_mutex.used_threads : sl_opacity typeclass_instances.

  Lemma test_mutex_ok :
    verify[source] "test_shared_mutex()".
  Proof.
    verify_spec; go.
    iExists (const emp); simpl.
    iSplit; first work.
    iIntros "[% [? H]]".
    iMod (shared_mutex.login thr g empty with "H") as "[??]"; first set_solver.
    wuntil Kfree go.
    rewrite /Kfree/=.
    iMod (shared_mutex.logout thr g empty with "[$]") as "?";first set_solver.
    go.
  Qed.

  (* TODO prove the rest of the tests *)
End with_cpp.
