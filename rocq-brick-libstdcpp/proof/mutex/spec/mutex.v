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

Import linearity.

Module mutex.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr="std::mutex")] derive R.
  #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

  (** Owning [mutex_token γ 1] proves that the mutex is not locked, and
  therefore can be safely destroyed: the standard specifies that calling
  [std::mutex::~mutex()] while holding the lock results in undefined behavior.
  *)
  Parameter token : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> Qp -> mpred.
  #[only(fractional,fracvalid,asfractional,timeless)] derive token.

  (** A resource enforcing that the thread calling unlock must be the same thread
      that owns the lock

    <<
    \persist{th} >={ L_TI } th
    \pre{j} mutex_locked g j
    test_unlock(std::mutex & m) {
      m.unlock();
    }
    >>

    this succeeds:

    <<
    \persist{th} >={ L_TI } th
    \pre mutex_locked g th
    same test_unlock
    >>
   *)
  Parameter locked : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      gname -> thread_idT -> Qp -> mpred.
  #[only(timeless)] derive locked.

  (** locked takes a [Qp] but _cannot_ be split. *)
  #[only(exclusive)] derive locked.

  Context `{MOD : source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  #[global] Instance locked_learn : Cbn (Learn (req_eq ==> learn_eq ==> learn_eq ==> learn_hints.fin) locked).
  Proof. solve_learnable. Qed.


  Definition do_unlock (lk : gname * mpred) (Q : mpred) : mpred :=
      match lk with
      | (g, P) =>
        Exists q thr, current_thread thr ** locked g thr q ** ▷P **
        (* TODO readd *)
        (* ▷ *)
        (token g q -* Q)
      end.
  #[global] Arguments do_unlock /.

  Definition do_lock (lk : gname * mpred) (K: mpred) : mpred :=
      match lk with
      | (g, P) =>
        ∃ q thr, current_thread thr ∗ token g q ∗
        (* TODO readd *)
        (* ▷ *)
        (locked g thr q ** ▷P -* K)
      end.
  #[global] Arguments do_lock /.

  cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\this this
      \pre{P} ▷P
      \post Exists g, this |-> R g 1$m P ** token g 1).

  (*
  Note: An alternative spec would take unrelated fractions for [R] and [token].
  That spec would be more expressive, but that expressiveness appears useless.
  See [recursive_mutex.lock_spec] for an example of the alternative. *)
  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre{q'} token g q'
      \post P ** locked g thr q').

  cpp.spec "std::mutex::lock()" as lock_spec_alt with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \pre{K} do_lock (g, P) K
      \post K
      ).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{th} current_thread th
      \pre token g q
      \post{b}[Vbool b] if b then P ** locked g th q else token g q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre{q'} locked g thr q'
      \pre ▷P
      \post token g q').

  cpp.spec "std::mutex::unlock()" as unlock_spec_alt with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \pre{K} do_unlock (g, P) K
      \post K).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \pre{g P} this |-> R g 1$m P ** token g 1
      \post P).

  Lemma lock_spec_entails_lock_spec_alt : lock_spec |-- lock_spec_alt.
  Proof.
    apply specify_mono.
    ework with br_erefl.
  Qed.


  Lemma unlock_spec_entails_unlock_spec_alt : unlock_spec |-- unlock_spec_alt.
  Proof.
    apply specify_mono.
    ework with br_erefl.
  Qed.

  (** <<std::mutex>> implements [BasicLockable] *)
  Definition T : Type := gname * mpred.

  (* TODO UPSTREAM. *)
  #[global] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

  #[global,program] Instance mutex_basic_lockable : BasicLockable (T:=T) "std::mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_lock := fun this => do_lock
  ; do_unlock := fun this => do_unlock }.

  cpp.spec "std::mutex::lock()" as lock_spec_alt' with
  (\exact Reduce (lock_basic_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  cpp.spec "std::mutex::unlock()" as unlock_spec_alt' with
  (\exact Reduce (unlock_basic_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  Lemma lock_spec_alt_equiv_lock_spec_alt' :
    lock_spec_alt -|- lock_spec_alt'.
  Proof.
    iSplit; iApply specify_mono; work with br_erefl;
      try case_match; ework with br_erefl.
  Qed.

  Lemma unlock_spec_alt_equiv_unlock_spec_alt' :
    unlock_spec_alt -|- unlock_spec_alt'.
  Proof.
    iSplit; iApply specify_mono; work with br_erefl;
      try case_match; ework with br_erefl.
  Qed.

  (*
  #[global,program] Instance mutex_basic_lockable : BasicLockable (T := gname * Qp * mpred) "std::mutex" (λ q '(thr, γ, q', P), R γ q$m P) :=
  { do_lock := fun this '(γ, q', P) K => do_lock thr (γ, q', P) K
  ; do_unlock := fun this '(γ, q', P) K => do_unlock thr (γ, q', P) K }.
  *)
End with_cpp.
End mutex.

