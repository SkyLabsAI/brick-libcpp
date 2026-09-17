Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.

Import linearity.

(** A MUTEX_PREDS says a mutex spec is parametrized by some `token`, `not_locked`
  and `locked`. The exact model depends on the implementation. *)

Module Type MUTEX_PREDS.
  Parameter gname : Set.
  Parameter cpp_ty : type.
  (** Mutex-set pool agreed before mutex creation. *)
  Parameter mutex_inv_namespace : namespace.

  Parameter G : forall `{Σ : cpp_logic}, Type.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.

  (** Registration uses the same mutex-set model as the state predicates. *)
  #[global] Declare Instance sets_G `{Σ : cpp_logic, !G Σ} : MutexSets.G Σ.

  (** [cQp.t] describes the permissions transferred by lock and unlock.
      The permission might involve points-to, so use cQp.t instead of QP. *)
  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    gname -> cQp.t -> mpred.
  Parameter not_locked locked : forall `{Σ : cpp_logic, !G Σ} {σ : genv},
    ptr -> gname -> thread_idT -> cQp.t -> mpred.

  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : CFractional (token γ).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  #[global] Declare Instance not_locked_timeless
      `{Σ : cpp_logic, !G Σ} {σ : genv} this γ th q :
    Timeless (not_locked this γ th q).
  (** Each thread has at most one handle to attempt locking this mutex. *)
  #[global] Declare Instance not_locked_exclusive
      `{Σ : cpp_logic, !G Σ} {σ : genv} this γ th :
    Exclusive1 (not_locked this γ th).
  #[global] Declare Instance locked_timeless
      `{Σ : cpp_logic, !G Σ} {σ : genv} this γ th q :
    Timeless (locked this γ th q).
  #[global] Declare Instance locked_exclusive
      `{Σ : cpp_logic, !G Σ} {σ : genv} this γ :
    Exclusive2 (locked this γ).

  (** The thread-registration pool used by this mutex. *)
  Parameter pool_name : gname -> iprop.gname.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (** Fractional ownership of a mutex guarding the predicate <<P>>. *)
    Parameter R : forall `{!G Σ} {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
    Context `{!G Σ}.
    #[global] Hint Opaque R : sl_opacity typeclass_instances.
    #[only(cfractional,cfracvalid,ascfractional)] derive R.
    (* #[global] Declare Instance R_type_ptr : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P,
      Typed class_name (R g q P). *)
    #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
        Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

    Context {σ : genv}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    #[global] Instance locked_learn :
        Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> req_eq ==> learn_hints.fin) locked).
    Proof. solve_learnable. Qed.

    (* TODO readd the later on the lock/unlock continuations. *)
    Definition do_lock (this : ptr) (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ thr qt, current_thread thr ** not_locked this lk.1 thr qt **
        (locked this lk.1 thr qt ** lk.2 -* K).
    #[global] Arguments do_lock /.

    Definition do_unlock (this : ptr) (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ thr qt, current_thread thr ** locked this lk.1 thr qt ** ▷lk.2 **
        (not_locked this lk.1 thr qt -* K).
    #[global] Arguments do_unlock /.

    #[global] Instance mutex_basic_lockable :
        BasicLockable (T := gname * mpred) cpp_ty
          (fun q gP => R gP.1 q gP.2) :=
      { do_lock := do_lock
      ; do_unlock := do_unlock }.

    Definition do_try_lock (this : ptr) (lk : gname * mpred)
        (K : bool -> mpred) : mpred :=
      ∃ thr qt, current_thread thr ** not_locked this lk.1 thr qt **
        ∀ b : bool,
          (if b then lk.2 ** locked this lk.1 thr qt
            else not_locked this lk.1 thr qt) -* K b.
    #[global] Arguments do_try_lock /.

    #[global] Instance mutex_lockable :
          Lockable (T:=gname * mpred) cpp_ty (λ q γP, R γP.1 q γP.2) :=
        { do_try_lock := do_try_lock }.

    (** Install [P] in an initialized mutex using its full representation and
        token. The physical mutex remains initialized and unlocked.
        
        Initializing [this |-> R old 1$m emp] probably depends on the mutex
        implementation. *)
    Parameter init_R : forall (this : ptr) (old : gname)
        (pool : iprop.gname) (P : mpred),
      WeaklyObjective P ->
      this |-> R old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g,
          [| pool_name g = pool |] **
          this |-> R g 1$m P ** token g 1$m).

    (** Register a thread by consuming its handle for this mutex's namespace
        and its token share. [my_mutexes_alloc_mutex_name] splits this handle
        from the full namespace pool supplied when the thread is spawned. *)
    Parameter register_thread : forall
        (this : ptr) (g : gname) (q : cQp.t) (P : mpred)
        (th : thread_idT) (qt : cQp.t),
      this |-> R g q P ** token g qt **
      MutexSets.my_mutexes (pool_name g) th
        (coPset.CoPset $ ↑mutex_inv_namespace) |--
      this |-> R g q P ** not_locked this g th qt.

  End with_cpp.
End MUTEX_PREDS.

(* TODO UPSTREAM. FIXME what does this do? *)
#[global] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

Module mutex_spec (Preds : MUTEX_PREDS).
Section with_cpp.
  Import Preds.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context `{!G Σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.


  (** The guarded predicate must be weakly objective for invariant allocation,
      which R likely has. *)
  Definition ctor_spec (this : ptr) : WpSpec mpred val val :=
    (\pre{P} ▷P
     \require WeaklyObjective P
     \post |={⊤}=> Exists g,
       this |-> R g 1$m P ** token g 1$m).

  Definition dtor_spec : ptr -> WpSpec mpred val val :=
    (\this this
      \pre{g P} this |-> R g 1$m P ** token g 1$m
      \post P).

  Definition lock_spec_alt : ptr -> WpSpec mpred val val :=
    (\this this
      \prepost{q P g} this |-> R g q P
      \persist{thr} current_thread thr
      \pre{qt} not_locked this g thr qt
      \post P ** locked this g thr qt).

  Definition unlock_spec_alt : ptr -> WpSpec mpred val val :=
    (\this this
      \prepost{q P g} this |-> R g q P
      \persist{thr} current_thread thr
      \pre{qt} locked this g thr qt
      \pre ▷P
      \post not_locked this g thr qt).

  Definition try_lock_spec_alt : ptr -> WpSpec mpred val val :=
    (\this this
      \prepost{q P g} this |-> R g q P
      \persist{thr} current_thread thr
      \pre{qt} not_locked this g thr qt
      \post{b}[Vbool b]
        if b then P ** locked this g thr qt
        else not_locked this g thr qt).

  Definition lock_spec : ptr -> WpSpec mpred val val :=
    lock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

  Definition unlock_spec : ptr -> WpSpec mpred val val :=
    unlock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

  Section equivalences.
    Lemma lock_spec_equiv_lock_spec_alt this xs K :
      lock_spec this xs K ⊣⊢ lock_spec_alt this xs K.
    Proof.
      unfold lock_spec, lock_basic_lockable.
      unfold lock_spec_alt, do_lock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HNL & HK)".
        iExists q, (g, P), (P ** Preds.locked this g thr qt)%I.
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HNL".
        iIntros "[HL HP]". iFrame.
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt this xs K :
      unlock_spec this xs K ⊣⊢ unlock_spec_alt this xs K.
    Proof.
      unfold unlock_spec, unlock_basic_lockable.
      unfold unlock_spec_alt, do_unlock.
      cbn. iSplit.
      - ework with br_erefl.
      - iIntros "H". iDestruct "H" as (q P g thr qt)
          "(%Hxs & HR & #HT & HL & HP & HK)".
        iExists q, (g, P), (Preds.not_locked this g thr qt).
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HL HP".
        iIntros "$".
    Qed.

    Definition try_lock_spec : ptr -> WpSpec mpred val val :=
      try_lock_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

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
          if b then (P ** Preds.locked this g thr qt)%I
          else Preds.not_locked this g thr qt).
        iFrame "HR HK". iSplit; first done.
        iExists thr, qt. iFrame "HT HNL".
        iIntros (b) "$".
    Qed.
  End equivalences.
End with_cpp.
End mutex_spec.


(** Specialize the reusable specs to the standard mutex representation and
    bind them to their C++ names. *)
Module StdMutex (Preds : MUTEX_PREDS with Definition cpp_ty := "std::mutex"%cpp_type).
  Include Preds.
  #[global] Hint Opaque token not_locked locked R : sl_opacity.

  Module Spec := mutex_spec Preds.

  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.

    (* FIXME can we delete this? *)
    Section with_RepFor.
      Import rep.RepFor.
      Import RepScheme.

      #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
        rep.RepFor.C "std::mutex" [ArgType.Constant _; ArgType.CFrac; ArgType.Constant _]
          (funI γ q P => R γ q P) := {}.
    End with_RepFor.

    Context `{MOD : source ⊧ σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\exact Reduce (Spec.ctor_spec)).

    cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\exact Reduce (Spec.dtor_spec)).

    cpp.spec "std::mutex::lock()" as lock_spec_alt with
      (\exact Reduce (Spec.lock_spec_alt)).

    cpp.spec "std::mutex::unlock()" as unlock_spec_alt with
      (\exact Reduce (Spec.unlock_spec_alt)).

    cpp.spec "std::mutex::try_lock()" as try_lock_spec_alt with
      (\exact Reduce (Spec.try_lock_spec_alt)).

    cpp.spec "std::mutex::lock()" as lock_spec with
      (\exact Reduce (Spec.lock_spec)).

    cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\exact Reduce (Spec.unlock_spec)).

    cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\exact Reduce (Spec.try_lock_spec)).

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
End StdMutex.

(** The standard-library implementation remains abstract; concrete mutex
    implementations supply their own [MUTEX_PREDS]. *)
Declare Module StdMutexPreds : MUTEX_PREDS with Definition cpp_ty := "std::mutex"%cpp_type.
Module mutex := StdMutex StdMutexPreds.
