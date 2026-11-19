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
Require Export skylabs.brick.libstdcpp.mutex.spec.base_mutex.
Export lock_ghost2.mutex_set_G (mutex_set_G).

Import linearity.

(** C++ mutex types: [BASE_MUTEX_PREDS] plus the BasicLockable and Lockable
    named requirements, which [std::unique_lock], [std::lock_guard] and
    [std::scoped_lock] use. *)
Module Type CPP_MUTEX_PREDS.
  Include BASE_MUTEX_PREDS.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.
    Context {σ : genv}.
    Context {HAS_THREADS : HasStdThreads Σ}.

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
  End with_cpp.
End CPP_MUTEX_PREDS.

(** The C++ contracts, including their BasicLockable and Lockable forms. *)
Module mutex_spec (Preds : CPP_MUTEX_PREDS).
  Include base_mutex_spec Preds.
Section with_cpp.
  Import Preds.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!G Σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

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
Module StdMutex (Preds : CPP_MUTEX_PREDS with Definition cpp_ty := "std::mutex"%cpp_type).
  Include Preds.
  #[global] Hint Opaque cpp_ty token not_locked locked R : sl_opacity.

  Module Spec := mutex_spec Preds.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.

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

    #[global] Instance R_std_type_ptr g q P :
      Observe (type_ptrR "std::mutex") (R g q P).
    Proof. apply R_type_ptr. Qed.

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
    implementations supply their own [CPP_MUTEX_PREDS]. *)
Declare Module StdMutexPreds : CPP_MUTEX_PREDS with Definition cpp_ty := "std::mutex"%cpp_type.
Module mutex := StdMutex StdMutexPreds.
