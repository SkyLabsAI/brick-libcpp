Require Import iris.algebra.coPset.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.

Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.shared_mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.

Import linearity.

(** Predicates for shared mutexes, independent of their implementation. *)
Module Type SHARED_MUTEX_PREDS.
  Parameter cpp_ty : type.
  Parameter gname : Set.
  Parameter G : forall `{Σ : cpp_logic}, Type.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.

  Parameter pool_name : gname -> iprop.gname.
  Parameter smutex_inv_namespace : gname -> namespace.
  #[global] Declare Instance sets_G `{Σ : cpp_logic, !G Σ} : MutexSets.G Σ.

  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    gname -> cQp.t -> mpred.
  Definition not_locked `{Σ : cpp_logic, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    token g qt ** MutexSets.my_mutexes (pool_name g) th
      (CoPset $ ↑smutex_inv_namespace g).

  Parameter locked : forall `{Σ : cpp_logic, !G Σ} {σ : genv},
    ptr -> gname -> thread_idT -> cQp.t -> mpred.
  (** [reader_locked this g th q qP] says it contains [token g q] and has
      borrowed [P qP] (but [reader_locked] does not include [P] itself). *)
  Parameter reader_locked : forall `{Σ : cpp_logic, !G Σ} {σ : genv},
    ptr -> gname -> thread_idT -> cQp.t -> Qp -> mpred.

  (**  A shared mutex guarding a fractional predicate [P]. *)
  Parameter R : forall `{Σ : cpp_logic, !G Σ}
    {HAS_THREADS : HasStdThreads Σ} {σ : genv},
    gname -> cQp.t -> (Qp -> mpred) -> Rep.
  #[global] Hint Opaque token not_locked locked reader_locked R :
    sl_opacity typeclass_instances.

  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.

    #[global] Declare Instance token_fractional g : CFractional (token g).
    #[global] Declare Instance token_timeless g qt : Timeless (token g qt).

    Context {σ : genv}.

    #[global] Instance not_locked_timeless this g th qt :
      Timeless (not_locked this g th qt).
    Proof. rewrite /not_locked. apply _. Qed.
    #[global] Instance not_locked_exclusive this g th :
      Exclusive1 (not_locked this g th).
    Proof.
      intros qt1 qt2. rewrite /not_locked.
      iIntros "[_ H1] [_ H2]".
      have Hoverlap : ~ ((↑smutex_inv_namespace g : coPset) ## ↑smutex_inv_namespace g).
      { have Hnonempty := nclose_non_empty (smutex_inv_namespace g). set_solver. }
      iDestruct (MutexSets.my_mutexes_exclusive _ th
        (↑smutex_inv_namespace g) (↑smutex_inv_namespace g) Hoverlap
        with "[$H1 $H2]") as %[].
    Qed.
    #[global] Declare Instance locked_timeless this g th qt :
      Timeless (locked this g th qt).
    #[global] Declare Instance locked_exclusive this g :
      Exclusive2 (locked this g).
    #[global] Declare Instance locked_objective this g th qt :
      Objective (locked this g th qt).
    #[global] Declare Instance reader_locked_timeless this g th qt qP :
      Timeless (reader_locked this g th qt qP).
    #[global] Declare Instance reader_locked_objective this g th qt qP :
      Objective (reader_locked this g th qt qP).

    Axiom reader_writer_exclusive : forall this g th1 th2 qt1 qt2 qP,
      th1 <> th2 ->
      reader_locked this g th1 qt1 qP -∗ locked this g th2 qt2 -∗ False.

    Context {HAS_THREADS : HasStdThreads Σ}.

    #[only(cfractional,cfracvalid,ascfractional)] derive R.
    #[global] Declare Instance R_type_ptr g q P :
      Observe (type_ptrR cpp_ty) (R g q P).
  End with_cpp.
End SHARED_MUTEX_PREDS.

(** Reusable contracts and their [BasicLockable]/[Lockable] presentation. *)
Module shared_mutex_spec (Preds : SHARED_MUTEX_PREDS).
  Import Preds.
  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.
    Context {HAS_THREADS : HasStdThreads Σ} {σ : genv}.

    (* ctor and dtor are the same as mutex.v, except that [P] is fractional. *)
    Definition ctor_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \pre{pool N P} ▷P 1%Qp
       \require Fractional P
       \require ∀ q, Objective (P q)
       \post Exists g,
         [| pool_name g = pool /\ smutex_inv_namespace g = N |] **
         this |-> R g 1$m P ** token g 1$m).

    Definition dtor_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \pre{g P} this |-> R g 1$m P ** token g 1$m
       \post P 1%Qp).

    Definition lock_spec_alt : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q P g} this |-> R g q P
       \persist{thr} current_thread thr
       \pre{qt} not_locked this g thr qt
       \post P 1%Qp ** locked this g thr qt).

    Definition unlock_spec_alt : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q P g} this |-> R g q P
       \persist{thr} current_thread thr
       \pre{qt} locked this g thr qt
       \pre ▷P 1%Qp
       \post not_locked this g thr qt).

    Definition try_lock_spec_alt : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q P g} this |-> R g q P
       \persist{thr} current_thread thr
       \pre{qt} not_locked this g thr qt
       \post{b}[Vbool b]
         if b then P 1%Qp ** locked this g thr qt
         else not_locked this g thr qt).

    Definition lock_shared_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q P g} this |-> R g q P
       \persist{thr} current_thread thr
       \pre{qt} not_locked this g thr qt
       \post ∃ qP, P qP ** reader_locked this g thr qt qP).

    Definition try_lock_shared_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q P g} this |-> R g q P
       \persist{thr} current_thread thr
       \pre{qt} not_locked this g thr qt
       \post{b}[Vbool b]
         if b then ∃ qP, P qP ** reader_locked this g thr qt qP
         else not_locked this g thr qt).

    Definition unlock_shared_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q P g} this |-> R g q P
       \persist{thr} current_thread thr
       \pre{qt qP} reader_locked this g thr qt qP
       \pre ▷P qP
       \post not_locked this g thr qt).

    Definition do_lock (this : ptr) (lk : gname * (Qp -> mpred))
        (K : mpred) : mpred :=
      ∃ thr qt, current_thread thr ** not_locked this lk.1 thr qt **
        (locked this lk.1 thr qt ** lk.2 1%Qp -* K).
    #[global] Arguments do_lock /.

    Definition do_unlock (this : ptr) (lk : gname * (Qp -> mpred))
        (K : mpred) : mpred :=
      ∃ thr qt, current_thread thr ** locked this lk.1 thr qt ** ▷lk.2 1%Qp **
        (not_locked this lk.1 thr qt -* K).
    #[global] Arguments do_unlock /.

    #[global] Instance shared_mutex_basic_lockable :
        BasicLockable (T := gname * (Qp -> mpred)) cpp_ty
          (fun q gP => R gP.1 q gP.2) :=
      { do_lock := do_lock
      ; do_unlock := do_unlock }.

    Definition do_try_lock (this : ptr) (lk : gname * (Qp -> mpred))
        (K : bool -> mpred) : mpred :=
      ∃ thr qt, current_thread thr ** not_locked this lk.1 thr qt **
        ∀ b : bool,
          (if b then lk.2 1%Qp ** locked this lk.1 thr qt
           else not_locked this lk.1 thr qt) -* K b.
    #[global] Arguments do_try_lock /.

    #[global] Instance shared_mutex_lockable :
        Lockable (T := gname * (Qp -> mpred)) cpp_ty
          (fun q gP => R gP.1 q gP.2) :=
      { do_try_lock := do_try_lock }.

    Definition lock_spec : ptr -> WpSpec mpred val val :=
      lock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

    Definition unlock_spec : ptr -> WpSpec mpred val val :=
      unlock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

    Definition try_lock_spec : ptr -> WpSpec mpred val val :=
      try_lock_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

    Lemma lock_spec_equiv_lock_spec_alt this xs K :
      lock_spec this xs K ⊣⊢ lock_spec_alt this xs K.
    Proof.
      unfold lock_spec, lock_basic_lockable, lock_spec_alt, do_lock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HNL & HK)".
        iExists q, (g, P), (P 1%Qp ** locked this g thr qt)%I.
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HNL".
        iIntros "[HL HP]". iFrame.
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt this xs K :
      unlock_spec this xs K ⊣⊢ unlock_spec_alt this xs K.
    Proof.
      unfold unlock_spec, unlock_basic_lockable, unlock_spec_alt, do_unlock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HL & HP & HK)".
        iExists q, (g, P), (not_locked this g thr qt).
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HL HP".
        iIntros "$".
    Qed.

    Lemma try_lock_spec_equiv_try_lock_spec_alt
        (Htry_lock : requirements.do_try_lock cpp_ty = do_try_lock) this xs K :
      try_lock_spec this xs K ⊣⊢ try_lock_spec_alt this xs K.
    Proof.
      unfold try_lock_spec, try_lock_lockable. rewrite Htry_lock.
      unfold try_lock_spec_alt, do_try_lock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HNL & HK)".
        iExists q, (g, P), (fun b : bool =>
          if b then (P 1%Qp ** locked this g thr qt)%I
          else not_locked this g thr qt).
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HNL".
        iIntros (b) "$".
    Qed.

    Section proof_automation.
      #[global] Instance R_learn :
        Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
      Proof. solve_learnable. Qed.
      #[global] Instance not_locked_learn this g th :
        LearnEq1 (not_locked this g th).
      Proof. solve_learnable. Qed.
      #[global] Instance locked_learn this g th :
        LearnEq1 (locked this g th).
      Proof. solve_learnable. Qed.
      #[global] Instance reader_locked_learn this g th :
        LearnEq2 (reader_locked this g th).
      Proof. solve_learnable. Qed.
    End proof_automation.
  End with_cpp.
End shared_mutex_spec.

(** Bind the reusable specifications to their standard C++ names. *)
Module StdSharedMutex
    (Preds : SHARED_MUTEX_PREDS with Definition cpp_ty := "std::shared_mutex"%cpp_type).
  Include Preds.
  #[global] Hint Opaque cpp_ty : sl_opacity.
  Module Spec := shared_mutex_spec Preds.

  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context `{MOD : source ⊧ σ}.

    cpp.spec "std::shared_mutex::shared_mutex()" as ctor_spec with
      (\exact Reduce Spec.ctor_spec).
    cpp.spec "std::shared_mutex::~shared_mutex()" as dtor_spec with
      (\exact Reduce Spec.dtor_spec).
    cpp.spec "std::shared_mutex::lock()" as lock_spec_alt with
      (\exact Reduce Spec.lock_spec_alt).
    cpp.spec "std::shared_mutex::try_lock()" as try_lock_spec_alt with
      (\exact Reduce Spec.try_lock_spec_alt).
    cpp.spec "std::shared_mutex::unlock()" as unlock_spec_alt with
      (\exact Reduce Spec.unlock_spec_alt).
    cpp.spec "std::shared_mutex::lock_shared()" as lock_shared_spec_alt with
      (\exact Reduce Spec.lock_shared_spec).
    cpp.spec "std::shared_mutex::try_lock_shared()" as try_lock_shared_spec_alt with
      (\exact Reduce Spec.try_lock_shared_spec).
    cpp.spec "std::shared_mutex::unlock_shared()" as unlock_shared_spec_alt with
      (\exact Reduce Spec.unlock_shared_spec).
    cpp.spec "std::shared_mutex::lock()" as lock_spec with
      (\exact Reduce Spec.lock_spec).
    cpp.spec "std::shared_mutex::unlock()" as unlock_spec with
      (\exact Reduce Spec.unlock_spec).
    cpp.spec "std::shared_mutex::try_lock()" as try_lock_spec with
      (\exact Reduce Spec.try_lock_spec).

    #[global] Instance R_std_type_ptr g q P :
      Observe (type_ptrR "std::shared_mutex") (R g q P).
    Proof. apply R_type_ptr. Qed.

    Lemma lock_spec_equiv_lock_spec_alt : lock_spec -|- lock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; intros this xs K;
        rewrite Spec.lock_spec_equiv_lock_spec_alt; done.
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt : unlock_spec -|- unlock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; intros this xs K;
        rewrite Spec.unlock_spec_equiv_unlock_spec_alt; done.
    Qed.

    Lemma try_lock_spec_equiv_try_lock_spec_alt : try_lock_spec -|- try_lock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; intros this xs K;
        rewrite Spec.try_lock_spec_equiv_try_lock_spec_alt; done.
    Qed.
  End with_cpp.
End StdSharedMutex.

(** Concrete implementations supply their own [SHARED_MUTEX_PREDS]. *)
Declare Module SharedMutexPreds : SHARED_MUTEX_PREDS
  with Definition cpp_ty := "std::shared_mutex"%cpp_type.
Module shared_mutex := StdSharedMutex SharedMutexPreds.
