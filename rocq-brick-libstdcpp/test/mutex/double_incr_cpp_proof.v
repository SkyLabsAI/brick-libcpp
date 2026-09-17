Require Import skylabs.auto.cpp.proof.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.thread.spec.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.double_incr_cpp.
Require Import skylabs.brick.libstdcpp.test.mutex.double_incr_ghost.

#[local] Hint Opaque double_incr_protocol.frac double_incr_protocol.protected
  double_incr_protocol.done double_incr_protocol.evenR : sl_opacity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!mutex.G Σ, !double_incr_protocol.G Σ}.

  cpp.spec "double_incr()" as double_incr_spec_body from source with (
    \prepost{g q γ} _global "m" |-> mutex.R g q
      (double_incr_protocol.protected γ (_global "x"))
    \persist{thr} current_thread thr
    \prepost{qt} mutex.not_locked (_global "m") g thr qt
    \pre double_incr_protocol.frac γ (1 / 2)
    \post double_incr_protocol.done γ (_global "x")).

  Lemma double_incr_ok : verify[source] "double_incr()".
  Proof.
    verify_spec; go.
    iExists q, (mutex.locked (_global "m") g thr qt **
      double_incr_protocol.protected γ (_global "x"))%I, qt.
    iFrame. iSplitR; first (iIntros "$").
    iIntros "[? [? ?]]".
    iDestruct (double_incr_protocol.prepare with "[$]") as "[Hx Hfinish]".
    iDestruct "Hx" as (n) "[? %Heven]".
    go.
    replace (n + 1 + 1)%Z with (n + 2)%Z by lia.
    iDestruct select (_global "x" |-> uintR _ _) as "Hx".
    iAssert (double_incr_protocol.evenR (_global "x")) with "[Hx]" as "Hx".
    { iExists (trim 32 (n + 2)). iFrame. iPureIntro.
      apply double_incr_protocol.trim_add_two_even. exact Heven. }
    iDestruct ("Hfinish" with "Hx") as "[? ?]".
    iExists q, (mutex.not_locked (_global "m") g thr qt), qt; go.
  Qed.

  (** The verification below is conditional on these objectivity properties
      of the thread model. They are explicit proof hypotheses. *)
  Context `{worker_spec_objective : !ObjectiveWith threadTI double_incr_spec_body}.
  Context `{even_weakly_objective :
    !WeaklyObjective (double_incr_protocol.evenR (_global "x"))}.
  Context `{shared_mutex_objective : ∀ g γ,
    ObjectiveWith threadTI (_global "m" |-> mutex.R g (1 / 2)$m
      (double_incr_protocol.protected γ (_global "x")))}.
  Context `{shared_token_objective : ∀ g,
    ObjectiveWith threadTI (mutex.token g (1 / 2)$m)}.

  #[local] Instance protected_weakly_objective γ :
    WeaklyObjective (double_incr_protocol.protected γ (_global "x")).
  Proof using Type even_weakly_objective.
    rewrite /double_incr_protocol.protected /double_incr_protocol.auth
      /double_incr_protocol.frac. apply _.
  Qed.

  (** Each worker receives half of the mutex ownership and a completion
      ticket. Its namespace handle comes from spawn. *)
  Definition worker_start (g : mutex.gname)
      (γ : double_incr_protocol.gname) : mpred :=
    _global "m" |-> mutex.R g (1 / 2)$m
      (double_incr_protocol.protected γ (_global "x")) **
    mutex.token g (1 / 2)$m ** double_incr_protocol.frac γ (1 / 2).

  #[local] Instance worker_start_objective g γ :
    ObjectiveWith threadTI (worker_start g γ).
  Proof using Type shared_mutex_objective shared_token_objective.
    rewrite /worker_start /double_incr_protocol.frac.
    apply sep_objective_with; first apply _.
    apply sep_objective_with; first apply _.
    apply objective_objective_with. apply _.
  Qed.

  #[local] Instance done_weakly_objective γ :
    WeaklyObjective (double_incr_protocol.done γ (_global "x")).
  Proof using Type even_weakly_objective.
    rewrite /double_incr_protocol.done /double_incr_protocol.auth. apply _.
  Qed.

  (** Register the child's mutex namespace, then invoke the verified worker
      contract in that child's thread context. *)
  Lemma worker_entry `{MOD : source ⊧ σ} g γ :
    double_incr_spec_body ** worker_start g γ |--
    ∀ child,
      MutexSets.my_mutexes (mutex.pool_name g) child (coPset.CoPset ⊤) -*
      wp_fptr (σ.(genv_tu).(types)) thread.spec.entry_type
        (_global "double_incr()") []
        (fun _ => double_incr_protocol.done γ (_global "x")).
  Proof using Type worker_spec_objective even_weakly_objective
    shared_mutex_objective shared_token_objective.
    iIntros "[#Hcode Hstart]" (child) "Hset".
    rewrite (objective_with_intro_exactly_at threadTI
      (wp_fptr (σ.(genv_tu).(types)) thread.spec.entry_type
        (_global "double_incr()") []
        (fun _ => double_incr_protocol.done γ (_global "x"))) child).
    iDestruct (monPred_atleast_exactly_at threadTI child) as "HT".
    iModIntro.
    iDestruct "Hstart" as "(Hm & Htoken & Hfrac)".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name (mutex.pool_name g)
      child ⊤ (↑mutex.mutex_inv_namespace) ltac:(set_solver)
      with "Hset") as "[Hrest Hname]".
    iDestruct (mutex.register_thread with "[$Hm $Htoken $Hname]")
      as "[Hm Hnotlocked]".
    iEval (unfold double_incr_spec_body, specify, unmaterialized_specR) in "Hcode".
    iApply (invoke.use_cptrR with "Hcode"). cbn.
    iSplitR; first done.
    iExists g, ((1 / 2)$m)%cQp, γ, child, ((1 / 2)$m)%cQp.
    iSplitR; first done. iFrame.
    iFrame "HT".
    iIntros "[HR [HNL HD]]" (v) "HV". iExact "HD".
  Qed.

  #[local] Hint Opaque worker_start thread.spec.spawned_threads_inv : sl_opacity.

  Definition thread_pool_namespace : namespace :=
    nroot .@@ "double_incr" .@ "threads".

  (** Global vars are given as preconditions.
      Assume the mutex is initialized with an empty invariant (assocaited with
      γold), which can later be updated to a new invariant with init_R. *)
  cpp.spec "main()" as main_spec from source with (
    \pre _global "x" |-> uintR 1$m 0
    \pre{γold} _global "m" |-> mutex.R γold 1$m emp ** mutex.token γold 1$m
    \post[Vint 0] double_incr_protocol.evenR (_global "x")).

  Lemma main_ok : verify[source] "main()".
  Proof using Type worker_spec_objective even_weakly_objective
    shared_mutex_objective shared_token_objective.
    verify_spec.
    let rec expose_globals :=
      first [iDestruct select (_global "x" |-> uintR 1$m 0) as "Hx"
            | progress go1; expose_globals] in
    expose_globals.
    iAssert (double_incr_protocol.evenR (_global "x")) with "[Hx]" as "Hx".
    { iExists 0. iFrame. done. }
    iMod (double_incr_protocol.alloc with "Hx") as (γ) "(HP & Hf1 & Hf2)".
    iDestruct select (_global "m" |-> mutex.R γold 1$m emp) as "Hm".
    iDestruct select (mutex.token γold 1$m) as "Htoken".
    iMod (thread.spec.spawned_threads_inv_alloc thread_pool_namespace)
      as (pool) "#Hpool".
    (* Logical invariant setup for the already initialized mutex. *)
    iMod (mutex.init_R (_global "m") γold pool
      (double_incr_protocol.protected γ (_global "x")) ltac:(apply _)
      with "[Hm Htoken HP]") as (g) "(%Hpool_name & Hm & Htoken)".
    { iFrame "Hm Htoken". iNext. done. }
    subst pool.
    iDestruct "Hm" as "[Hm1 Hm2]".
    iEval (rewrite (cfractional_split_half (mutex.token g))
      cQp.scale_mut Qp.mul_1_r) in "Htoken".
    iDestruct "Htoken" as "[Ht1 Ht2]".
    iAssert (worker_start g γ ** worker_start g γ)%I
      with "[Hm1 Hm2 Ht1 Ht2 Hf1 Hf2]" as "[Hstart1 Hstart2]".
    { rewrite /worker_start. iFrame. }
    go.
    iDestruct select double_incr_spec_body as "#Hcode".
    iExists thread_pool_namespace, (mutex.pool_name g),
      (double_incr_protocol.done γ (_global "x")).
    iFrame "#". iSplitR; first (iPureIntro; apply _).
    iSplitL "Hstart1".
    - iApply worker_entry. iFrame "Hcode Hstart1".
    - iIntros "Hthread1".
      iDestruct "Hthread1" as (child1) "[% HR1]".
      iDestruct (observe (type_ptr "std::thread" t1_addr) with "HR1") as "#?".
      iDestruct "HR1" as "?". go.
      iExists thread_pool_namespace, (mutex.pool_name g),
        (double_incr_protocol.done γ (_global "x")).
      iFrame "#". iSplitR; first (iPureIntro; apply _).
      iSplitL "Hstart2".
      + iApply worker_entry. iFrame "Hcode Hstart2".
      + iIntros "Hthread2".
        iDestruct "Hthread2" as (child2) "[% HR2]".
        iDestruct (observe (type_ptr "std::thread" t2_addr) with "HR2") as "#?".
        iDestruct "HR2" as "?". go.
        iExists child1, (double_incr_protocol.done γ (_global "x")). go.
        iExists child2, (double_incr_protocol.done γ (_global "x")). go.
        iDestruct (double_incr_protocol.join with "[$]")
          as (n) "[Hx %Heven]".
        go.
        iExists (1$m)%cQp; go.
        iFrame.
        iExists n. iFrame. done.
  Qed.
End with_cpp.
