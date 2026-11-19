(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * SPDX-License-Identifier: BSD-3-Clause
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.base_derived.
Require Import skylabs.brick.libstdcpp.pthread.mutex.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.atomic.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.custom_mutex_hpp.
NES.Open std.atomic.

Import linearity.

(** The spinlock of custom_mutex.hpp, as a [BASE_MUTEX_PREDS] instance. Like
    glibc's mutex, it uses the owner-tracking invariant of [OwnerTidMutex];
    its physical state is the atomic [m_lock] field rather than abstract
    bytes. *)
Module CustomPthreadMutexPreds <: BASE_MUTEX_PREDS.
  Include OwnerTidMutex.

  Definition class_name : name := "my_mutex_t"%cpp_name.
  Definition cpp_ty : type := Tnamed class_name.

  Definition lockR `{Σ : cpp_logic, σ : genv} (this : ptr) (b : bool) : mpred :=
    this ,, _field "my_mutex_t::m_lock" |-> atomic.R "int" 1$m (if b then 1 else 0)%Z.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
    WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.

  #[global] Instance lockR_WeaklyObjective `{Σ : cpp_logic, σ : genv} this b :
    WeaklyObjective (lockR this b).
  Proof. rewrite /lockR. apply _. Qed.
  #[global] Instance lockR_timeless `{Σ : cpp_logic, σ : genv} this b :
    Timeless (lockR this b).
  Proof. rewrite /lockR. apply _. Qed.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.

    Definition R {HAS_THREADS : HasStdThreads Σ} {σ : genv}
        (g : gname) (q : cQp.t) (P : mpred) : Rep :=
      structR class_name q$m **
      as_Rep (fun this => cinv (mutex_inv_namespace g) g.(inv_gname) (state lockR this g P)) **
      pureR (cinv_own g.(inv_gname) q).
    #[global] Hint Opaque R : sl_opacity typeclass_instances.
    #[only(type_ptr,cfractional,ascfractional,cfracvalid)] derive R.

    Lemma R_mutexR {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P :
      R g q P = mutexR (fun q => structR class_name q$m) lockR g q P.
    Proof. reflexivity. Qed.

    #[global] Instance R_learnable {HAS_THREADS : HasStdThreads Σ} {σ : genv} :
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    Context {σ : genv}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    Lemma init_R (this : ptr) (old : gname) (N : namespace) (P : mpred) :
      WeaklyObjective P ->
      N <> nroot ->
      this |-> R old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g,
          [| mutex_inv_namespace g = N |] **
          this |-> R g 1$m P ** token g 1$m).
    Proof.
      intros. by apply (mutexR_reinit (fun q => structR class_name q$m) lockR); [apply _|..].
    Qed.

    Lemma locked_my_mutexes_exclusive (this : ptr) g th q qt P E :
      ↑mutex_inv_namespace g ⊆ E ->
      this |-> R g q P ** locked this g th qt **
        MutexSets.my_mutexes th
          (coPset.CoPset $ ↑mutex_inv_namespace g) |-- (|={E}=> False).
    Proof. rewrite R_mutexR. apply mutexR_locked_my_mutexes_exclusive. Qed.
  End with_cpp.
End CustomPthreadMutexPreds.

(** Verify the implementation against the same contracts as glibc's mutex,
    and its constructor and destructor against those of std::mutex. *)
Module custom_pthread_mutex.
  Import CustomPthreadMutexPreds.
  Module Spec := pthread_mutex_spec CustomPthreadMutexPreds.

  Abbreviation IR := CustomPthreadMutexPreds.R.
  Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

  (** The default memory order argument reads this global. *)
  Definition globals `{Σ : cpp_logic} {σ : genv} (q : cQp.t) : mpred :=
    _global "std::memory_order_seq_cst" |->
      primR "enum std::memory_order" q
        (memory_order.to_val memory_order.seq_cst).
  #[global] Arguments globals /.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!CustomPthreadMutexPreds.G Σ}.
    Context `{MOD : source ⊧ σ}.

    cpp.spec "my_mutex_t::my_mutex_t()" as ctor_spec with
      (\exact Reduce (Spec.ctor_spec)).
    cpp.spec "my_mutex_t::~my_mutex_t()" as dtor_spec with
      (\exact Reduce (Spec.dtor_spec)).
    cpp.spec "my_mutex_lock(my_mutex_t*)" as lock_owned_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.lock_owned_spec).
    cpp.spec "my_mutex_lock(my_mutex_t*)" as lock_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.lock_spec).
    cpp.spec "my_mutex_unlock(my_mutex_t*)" as unlock_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.unlock_spec).
    cpp.spec "my_mutex_trylock(my_mutex_t*)" as trylock_owned_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.trylock_owned_spec).
    cpp.spec "my_mutex_trylock(my_mutex_t*)" as trylock_held_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.trylock_held_spec).
    cpp.spec "my_mutex_trylock(my_mutex_t*)" as trylock_uncontended_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.trylock_uncontended_spec).
    cpp.spec "my_mutex_trylock(my_mutex_t*)" as trylock_spec with
      (\prepost{qg} globals qg \exact Reduce Spec.trylock_spec).

    Definition bi_later_exist_F := [FWD] @bi.later_exist.
    Definition bi_later_sep_F := [FWD] @bi.later_sep.
    Hint Resolve bi_later_exist_F bi_later_sep_F : br_hints.

    (** Exchanging 1 into [m_lock] while holding [not_locked]: acquire if it
        was 0. *)
    #[program]
    Definition do_exchange_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming{qt} not_locked p g thr qt
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p ,, o_field σ "my_mutex_t::m_lock")) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 0 \/ res = 1 |]%Z **
                          if bool_decide (res = 0) then P ** locked p g thr qt
                          else not_locked p g thr qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & NL)".
      iEval (rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv (mutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /state) in "Inv".
      iDestruct "Inv" as (owner) "(>L & >Auth & Rest)".
      iEval (rewrite /lockR) in "L".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if bool_decide (is_Some owner) then 1 else 0)%Z.
      iSplitL "L".
      { ework $usenamed=true with br_erefl. }
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L Auth Rest]") as "_".
        { iNext. rewrite /state /lockR. iExists owner.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros "L". iMod "Y" as "_".
        destruct owner as [[th' qt']|].
        + iMod ("Hclose" with "[L Auth Rest]") as "_".
          { iNext. rewrite /state /lockR. iExists (Some (th', qt')).
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iFrame. }
          iModIntro. rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR /=.
          iFrame "CI". iFrame. iPureIntro. auto.
        + iDestruct "Rest" as "[F P]".
          iMod (state_acquire with "[$Auth $F $NL]") as "(Auth & NL & Lk)".
          iMod ("Hclose" with "[L Auth NL]") as "_".
          { iNext. rewrite /state /lockR. iExists (Some (thr, qt)).
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iFrame. }
          iModIntro. rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR /=.
          iFrame "CI". iFrame. iPureIntro. auto.
    Qed.
    Hint Resolve do_exchange_C : sl_opacity.

    (** Storing 0 into [m_lock] as its owner: release. *)
    #[program]
    Definition do_store_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming P
      \consuming{(qt : cQp.t)} locked p g thr qt
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store "int" (BASE (p ,, o_field σ "my_mutex_t::m_lock")) 0%Z K
      \instantiate K := (p |-> IR g q P ** not_locked p g thr qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & P & Locked)".
      iEval (rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc /=.
      iInv (mutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /state) in "Inv".
      iDestruct "Inv" as (owner) "(>L & >Auth & Rest)".
      iEval (rewrite /lockR) in "L".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if bool_decide (is_Some owner) then 1 else 0)%Z.
      iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      iMod (state_release with "[$Auth $Locked]") as "(-> & Auth & F)".
      iMod ("Hclose" with "[L Auth F P]") as "_".
      { iNext. rewrite /state /lockR. iExists None.
        iSplitL "L"; first by ework $usenamed=true with br_erefl.
        iFrame. }
      iModIntro. rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR /=.
      iFrame "CI". iFrame.
    Qed.
    Hint Resolve do_store_C : sl_opacity.

    (** Choose the success flag of a trylock postcondition. *)
    #[local] Ltac pick_success v :=
      match goal with |- context [if ?b then _ else _] => is_evar b; unify b v end.

    Lemma ctor_ok : verify[source] "my_mutex_t::my_mutex_t()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wname [P] "P".
      wname [_ |-> atomic.R _ _ _] "L".
      wname [structR] "S".
      iMod (mutexR_alloc (fun q => structR class_name q$m) lockR this N P
        ltac:(intros; apply _) H1 H0 with "[S L P]") as (g) "(% & HR & T)".
      { iFrame "P". iSplitL "S"; first iExact "S".
        rewrite /lockR /=. iFrame "L".
        rewrite -bi.later_sep bi.emp_sep -bi.later_intro. done. }
      iExists g. rewrite R_mutexR. iFrame "HR T". by iPureIntro.
    Qed.

    Lemma dtor_ok : verify[source] "my_mutex_t::~my_mutex_t()".
    Proof using MOD HAS_THREADS.
      verify_spec. work.
      wname [_ |-> IR _ _ _] "HR".
      wname [token] "T".
      rewrite R_mutexR.
      iMod (mutexR_cancel_timeless (fun q => structR class_name q$m) lockR
        this g P ltac:(intros; apply _) with "[$HR $T]") as "(? & ? & ?)".
      rewrite /lockR /=. go.
    Qed.

    Lemma unlock_ok : verify[source] unlock_spec.
    Proof using MOD HAS_THREADS. verify_spec; ego. Qed.

    Lemma trylock_ok : verify[source] trylock_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
      repeat (first [case_bool_decide | wp_if]; ego).
      all: first [ pick_success true; go; done
                 | pick_success false; rewrite /pthread_errno.EBUSY; go; done ].
    Qed.

    Lemma lock_ok : verify[source] lock_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
      wp_while (fun _ => emp); ego.
      repeat (first [case_bool_decide | wp_if]; ego).
    Qed.

    (** ** Rules specific to the default (NORMAL) mutex type *)

    (** Exchanging 1 into a held [m_lock]: it stays held, by the same owner.
        The caller need not be the owner. *)
    #[program]
    Definition do_exchange_held_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{g q P} p |-> IR g q P
      \consuming{th qt} locked p g th qt
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p ,, o_field σ "my_mutex_t::m_lock")) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 1 |]%Z ** locked p g th qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(IR & Lk)".
      iEval (rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv (mutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /state) in "Inv".
      iDestruct "Inv" as (owner) "(>L & >Auth & Rest)".
      iEval (rewrite /lockR) in "L".
      iEval (rewrite /locked) in "Lk".
      iDestruct (observe_2 [| owner = Some (th, qt) |] with "Auth Lk") as %->.
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists 1%Z.
      iSplitL "L".
      { ework $usenamed=true with br_erefl. }
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L Auth Rest]") as "_".
        { iNext. rewrite /state /lockR. iExists (Some (th, qt)).
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. rewrite /locked. iFrame.
      - iNext. iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L Auth Rest]") as "_".
        { iNext. rewrite /state /lockR. iExists (Some (th, qt)).
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR /locked /=.
        iFrame "CI". iFrame. done.
    Qed.
    Hint Resolve do_exchange_held_C : sl_opacity.

    Lemma lock_owned_ok : verify[source] lock_owned_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
      wp_while (fun _ => emp); ego.
    Qed.

    Lemma trylock_owned_ok : verify[source] trylock_owned_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
    Qed.

    Lemma trylock_held_ok : verify[source] trylock_held_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
    Qed.

    (** With the full [IR] share and the full lifetime token, nobody holds the
        mutex: exchanging 1 into [m_lock] acquires it. *)
    #[program]
    Definition do_exchange_uncontended_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g P} p |-> IR g 1$m P
      \consuming not_locked p g thr 1$m
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p ,, o_field σ "my_mutex_t::m_lock")) 1%Z K
      \instantiate K := (fun res => p |-> IR g 1$m P ** [| res = 0 |]%Z **
                          P ** locked p g thr 1$m)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & NL)".
      iEval (rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv (mutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /state) in "Inv".
      iDestruct "Inv" as (owner) "(>L & >Auth & Rest)".
      iEval (rewrite /lockR) in "L".
      destruct owner as [[th' qt']|].
      { iMod "Rest". iEval (rewrite /not_locked /token) in "Rest NL".
        iDestruct "Rest" as "[Held Hm1]". iDestruct "NL" as "[T Hm2]".
        iDestruct (MutexTokens.token_valid_2 with "[$T $Held]") as %Hbad.
        exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt') Hbad). }
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists 0%Z.
      iSplitL "L".
      { ework $usenamed=true with br_erefl. }
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L Auth Rest]") as "_".
        { iNext. rewrite /state /lockR. iExists None.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros "L". iMod "Y" as "_".
        iDestruct "Rest" as "[F P]".
        iMod (state_acquire with "[$Auth $F $NL]") as "(Auth & NL & Lk)".
        iMod ("Hclose" with "[L Auth NL]") as "_".
        { iNext. rewrite /state /lockR. iExists (Some (thr, 1$m%cQp)).
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. rewrite R_mutexR /mutexR !_at_sep _at_as_Rep _at_pureR /=.
        iFrame "CI". iFrame. done.
    Qed.

    Section uncontended.
      #[local] Remove Hints do_exchange_C : sl_opacity.
      #[local] Hint Resolve do_exchange_uncontended_C : sl_opacity.

      Lemma trylock_uncontended_ok : verify[source] trylock_uncontended_spec.
      Proof using MOD HAS_THREADS.
        verify_spec; ego.
      Qed.
    End uncontended.
  End with_cpp.
End custom_pthread_mutex.
