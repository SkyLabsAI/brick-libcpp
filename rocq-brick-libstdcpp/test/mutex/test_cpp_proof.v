Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.test.mutex.test_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ, !mutex.G Σ}.

  cpp.spec "test_mutex()" as test_mutex_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Theorem test_mutex_ok : verify[source] "test_mutex()".
  Proof.
    verify_spec; go.
    iExists emp.
    let rec expose_init :=
      first [iDestruct select ((|={⊤}=> _)%I) as "Hinit"
            | progress go1; expose_init] in
    expose_init.
    iMod "Hinit" as (g) "[Hm Htoken]".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    iAssert (mutex.not_locked m_addr g thr (1$m)%cQp)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /mutex.not_locked. iFrame. }
    go $usenamed=true.
    iExists (mutex.locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iExists (mutex.not_locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iDestruct select (mutex.not_locked _ _ _ _) as "Hnotlocked".
    iEval (rewrite /mutex.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$Hrest $Hname]") as "Hnames".
    go $usenamed=true.
  Qed.

  cpp.spec "test_lock_guard()" as test_lock_guard_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Lemma test_lock_guard_ok : verify[source] "test_lock_guard()".
  Proof.
    verify_spec; go.
    iExists emp.
    let rec expose_init :=
      first [iDestruct select ((|={⊤}=> _)%I) as "Hinit"
            | progress go1; expose_init] in
    expose_init.
    iMod "Hinit" as (g) "[Hm Htoken]".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    iAssert (mutex.not_locked m_addr g thr (1$m)%cQp)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /mutex.not_locked. iFrame. }
    go $usenamed=true.
    iExists (mutex.locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iExists (mutex.not_locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iDestruct select (mutex.not_locked _ _ _ _) as "Hnotlocked".
    iEval (rewrite /mutex.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$Hrest $Hname]") as "Hnames".
    go $usenamed=true.
  Qed.

  cpp.spec "test_scoped_lock()" as test_scoped_lock_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Lemma test_scoped_lock_ok : verify[source] "test_scoped_lock()".
  Proof.
    verify_spec; go.
    iExists emp; go.
    iExists emp.
    let rec open_init :=
      first [(iDestruct select ((|={⊤}=> _)%I) as "Hinit";
              iMod "Hinit" as (g2) "[Hm2 Htoken2]")
            | progress go1; open_init] in
    open_init.
    iDestruct select ((|={⊤}=> _)%I) as "Hinit".
    iMod "Hinit" as (g1) "[Hm1 Htoken1]".
    iMod (mutex.init_R m1_addr g1 (nroot .@@ "test_scoped_lock" .@ "first") emp
      ltac:(apply _) with "[$Hm1 $Htoken1]") as (g1') "(%HN1 & Hm1 & Htoken1)".
    { done. }
    iMod (mutex.init_R m2_addr g2 (nroot .@@ "test_scoped_lock" .@ "second") emp
      ltac:(apply _) with "[$Hm2 $Htoken2]") as (g2') "(%HN2 & Hm2 & Htoken2)".
    { done. }
    have Hdisjoint : (↑mutex.mutex_inv_namespace g1' : coPset) ##
        ↑mutex.mutex_inv_namespace g2'.
    { rewrite HN1 HN2. solve_ndisj. }
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g1') ltac:(set_solver)
      with "[$]") as "[Hrest Hname1]".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name thr
      (⊤ ∖ ↑mutex.mutex_inv_namespace g1')
      (↑mutex.mutex_inv_namespace g2') ltac:(set_solver)
      with "Hrest") as "[Hrest Hname2]".
    iAssert (mutex.not_locked m1_addr g1' thr (1$m)%cQp)
      with "[Htoken1 Hname1]" as "Hnotlocked1".
    { rewrite /mutex.not_locked. iFrame. }
    iAssert (mutex.not_locked m2_addr g2' thr (1$m)%cQp)
      with "[Htoken2 Hname2]" as "Hnotlocked2".
    { rewrite /mutex.not_locked. iFrame. }
    go $usenamed=true.
    iExists (mutex.locked m1_addr g1' thr (1$m)%cQp),
      (mutex.locked m2_addr g2' thr (1$m)%cQp), (1$m)%cQp, (1$m)%cQp.
    go $usenamed=true.
    iExists (mutex.not_locked m1_addr g1' thr (1$m)%cQp),
      (mutex.not_locked m2_addr g2' thr (1$m)%cQp), (1$m)%cQp, (1$m)%cQp.
    go $usenamed=true.
    iDestruct select (mutex.not_locked m1_addr _ _ _) as "Hnotlocked1".
    iDestruct select (mutex.not_locked m2_addr _ _ _) as "Hnotlocked2".
    iEval (rewrite /mutex.not_locked) in "Hnotlocked1".
    iEval (rewrite /mutex.not_locked) in "Hnotlocked2".
    iDestruct "Hnotlocked1" as "[Htoken1 Hname1]".
    iDestruct "Hnotlocked2" as "[Htoken2 Hname2]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name thr
      (⊤ ∖ ↑mutex.mutex_inv_namespace g1')
      (↑mutex.mutex_inv_namespace g2') ltac:(set_solver)
      with "[$Hrest $Hname2]") as "Hrest".
    iDestruct (MutexSets.my_mutexes_join_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g1') ltac:(set_solver)
      with "[$Hrest $Hname1]") as "Hnames".
    go $usenamed=true.
  Qed.

  cpp.spec "test_unique_lock()" as test_unique_lock_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Lemma test_unique_lock_ok : verify[source] "test_unique_lock()".
  Proof.
    verify_spec; go.
    iExists emp.
    let rec expose_init :=
      first [iDestruct select ((|={⊤}=> _)%I) as "Hinit"
            | progress go1; expose_init] in
    expose_init.
    iMod "Hinit" as (g) "[Hm Htoken]".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    iAssert (mutex.not_locked m_addr g thr (1$m)%cQp)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /mutex.not_locked. iFrame. }
    go $usenamed=true.
    iExists (mutex.locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iExists (mutex.not_locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iDestruct select (mutex.not_locked _ _ _ _) as "Hnotlocked".
    iEval (rewrite /mutex.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$Hrest $Hname]") as "Hnames".
    go $usenamed=true.
  Qed.


  cpp.spec "test_unique_lock_defer()" as test_unique_lock_defer_spec from source with (
    \prepost{q} _global "std::defer_lock" |-> defer_lock_t.R q
    \post emp).

  Lemma test_unique_lock_defer_ok : verify[source] "test_unique_lock_defer()".
  Proof.
    verify_spec; go.
    iExists emp.
    let rec open_init :=
      first [(iDestruct select ((|={⊤}=> _)%I) as "Hinit";
              iMod "Hinit" as (g) "[Hm Htoken]")
            | progress go1; open_init] in
    open_init.
    go $usenamed=true.
  Qed.

  cpp.spec "std::move<std::unique_lock<std::mutex>&>(std::unique_lock<std::mutex>&)" from source inline.

  cpp.spec "test_unique_lock_move()" as test_unique_lock_move_spec from source with (
    \persist{thr} current_thread thr
    \prepost MutexSets.my_mutexes thr (coPset.CoPset ⊤)
    \post emp).

  Lemma test_unique_lock_move_ok : verify[source] "test_unique_lock_move()".
  Proof.
    verify_spec; go.
    iExists emp.
    let rec expose_init :=
      first [iDestruct select ((|={⊤}=> _)%I) as "Hinit"
            | progress go1; expose_init] in
    expose_init.
    iMod "Hinit" as (g) "[Hm Htoken]".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    iAssert (mutex.not_locked m_addr g thr (1$m)%cQp)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /mutex.not_locked. iFrame. }
    go $usenamed=true.
    iExists (mutex.locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iExists (mutex.not_locked m_addr g thr (1$m)%cQp), (1$m)%cQp.
    go $usenamed=true.
    iDestruct select (mutex.not_locked _ _ _ _) as "Hnotlocked".
    iEval (rewrite /mutex.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name thr ⊤
      (↑mutex.mutex_inv_namespace g) ltac:(set_solver)
      with "[$Hrest $Hname]") as "Hnames".
    go $usenamed=true.
  Qed.
End with_cpp.
