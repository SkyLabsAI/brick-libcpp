Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.spec.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

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
      \pre token g q
      \post P ** locked g thr q).

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
      \pre locked g thr q
      \pre ▷P
      \post token g q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \pre{g P} this |-> R g 1$m P ** token g 1
      \post P).

End with_cpp.
End mutex.

