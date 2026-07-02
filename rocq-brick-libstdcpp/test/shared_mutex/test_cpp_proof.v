Require Import skylabs.auto.cpp.prelude.proof.
(* Require Import skylabs.brick.libstdcpp.mutex.spec. *)
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

  (** WIP proof with easier specs *)
  Lemma test_mutex_ok :
    denoteModule source **
    shared_mutex.lock_spec_alt **
    shared_mutex.unlock_spec_alt **
    shared_mutex.dtor_spec **
    shared_mutex.ctor_spec
    |--
    test_mutex_spec.
    (* verify[source] "test_shared_mutex()". *)
  Proof.
    (* TODO: hacky proof *)
    verify_shift; go.
    iExists (const emp); simpl.
    iSplit; first work.
    iIntros "[% [? H]]".
    iMod (shared_mutex.login thr g empty with "H") as "[??]"; first set_solver.

    go.

    iPoseProof (shared_mutex.logout thr g empty with "[$]") as "H"; first set_solver.
    iSplitR "H"; last admit.

    go.

    iModIntro; go.
  Admitted.

End with_cpp.
