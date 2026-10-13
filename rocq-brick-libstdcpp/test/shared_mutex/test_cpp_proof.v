Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.shared_mutex.shared_mutex.
Require Import skylabs.brick.libstdcpp.test.shared_mutex.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!shared_mutex.G Σ}.

  cpp.spec "test_shared_mutex()" as test_shared_mutex_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Lemma test_shared_mutex_ok :
    verify[source] "test_shared_mutex()".
  Proof.
    verify_spec; go.
    iExists (nroot .@@ "test_shared_mutex"), (const emp); go.
    rename t into g.
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name
      thr ⊤
      (↑shared_mutex.smutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    wname [shared_mutex.token] "Htoken".
    iAssert (shared_mutex.not_locked m_addr g thr 1$m)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /shared_mutex.not_locked. iFrame. }
    iDestruct "Hnotlocked" as "?".
    iExists (1$m)%cQp, (g, const emp),
      (shared_mutex.locked m_addr g thr 1$m), (1$m)%cQp.
    go.
    iExists (1$m)%cQp, (g, const emp),
      (shared_mutex.not_locked m_addr g thr 1$m), (1$m)%cQp.
    go.
    wname [shared_mutex.not_locked] "Hnotlocked".
    iEval (rewrite /shared_mutex.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name
      thr ⊤
      (↑shared_mutex.smutex_inv_namespace g) ltac:(set_solver)
      with "[Hrest Hname]") as "Hnames"; first iFrame.
    go $usenamed=true.
  Qed.

  cpp.spec "test_shared_mutex_shared()" as test_mutex_shared_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Lemma test_shared_mutex_shared :
    verify[source] "test_shared_mutex_shared()".
  Proof.
    verify_spec; go.
    iExists (nroot .@@ "test_shared_mutex_shared"), (const emp); go.
    rename t into g.
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name
      thr ⊤
      (↑shared_mutex.smutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    wname [shared_mutex.token] "Htoken".
    iAssert (shared_mutex.not_locked m_addr g thr 1$m)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /shared_mutex.not_locked. iFrame. }
    iDestruct "Hnotlocked" as "?".
    go.
    wname [shared_mutex.not_locked] "Hnotlocked".
    iEval (rewrite /shared_mutex.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name
      thr ⊤
      (↑shared_mutex.smutex_inv_namespace g) ltac:(set_solver)
      with "[Hrest Hname]") as "Hnames"; first iFrame.
    go $usenamed=true.
  Qed.

  (* TODO prove the rest of the tests *)
End with_cpp.
