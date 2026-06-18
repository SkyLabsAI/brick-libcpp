Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.shared_mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.mutex.requirements.

Import linearity.

(* TODO UPSTREAM. *)
#[global] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

Module shared_mutex.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::shared_mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> (Qp -> mpred) -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr="std::shared_mutex")] derive R.
  #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

  (** Owning [token γ 1] proves that the shared_mutex is not locked, and
  therefore can be safely destroyed: the standard specifies that calling
  <std::shared_mutex::~shared_mutex()> while holding the lock results in
  undefined behavior.
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
      gname -> thread_idT -> option (Qp * option Qp) -> mpred.
  #[only(timeless)] derive locked.

  (** locked takes a [Qp] but _cannot_ be split. *)
  #[only(exclusive)] derive locked.

  Context `{MOD : source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  #[global] Instance locked_learn : Cbn (Learn (req_eq ==> learn_eq ==> learn_eq ==> learn_hints.fin) locked).
  Proof. solve_learnable. Qed.

  Parameter used_threads : gname -> gset thread_idT -> mpred.

  Lemma use_thread th g s :
    th ∉ s ->
     used_threads g s |--
    |==> used_threads g (s ∪ {[ th ]}) ** locked g th None.
  Proof. Abort.

  cpp.spec "std::shared_mutex::shared_mutex()" as ctor_spec with (
    \this this
    \pre{P} ▷P 1%Qp
    \post Exists g, this |-> R g 1$m P ** token g 1 ** used_threads g ∅).

  cpp.spec "std::shared_mutex::~shared_mutex()" as dtor_spec with (
    \this this
    \pre{g P} this |-> R g 1$m P ** token g 1
    \post P 1%Qp).

  (* "Inline" version of these specs. *)
  cpp.spec "std::shared_mutex::lock()" as lock_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{thr} current_thread thr
    \pre{q'} token g q'
    \pre locked g thr None
    \post P 1%Qp ** locked g thr (Some (q', None))).

  cpp.spec "std::shared_mutex::unlock()" as unlock_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{thr} current_thread thr
    \pre{q'} locked g thr (Some (q', None))
    \pre ▷ P 1%Qp
    \post locked g thr None ** token g q').

  cpp.spec "std::shared_mutex::lock_shared()" as lock_shared_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{thr} current_thread thr
    \pre locked g thr None
    \pre{q'} token g q'
    \post ∃ qP, P qP ** locked g thr (Some (q', Some qP))).

  cpp.spec "std::shared_mutex::unlock_shared()" as unlock_shared_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{thr} current_thread thr
    \pre{q' qP} locked g thr (Some (q', Some qP))
    \pre{qP} ▷P qP
    \post locked g thr None ** token g q').

  (*
  Definition do_lock (lk : gname * (Qp -> mpred)) (K: mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ q thr, current_thread thr ∗ token g q ∗
               (* TODO readd *)
               (* ▷ *)
               (locked g thr q ** P -* K).
  #[global] Arguments do_lock /.



  Definition do_unlock (lk : gname * mpred) (Q : mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    Exists q thr, current_thread thr ** locked g thr q ** ▷P **
    (* TODO readd *)
    (* ▷ *)
    (token g q -* Q).
  #[global] Arguments do_unlock /.

  cpp.spec "std::shared_mutex::try_lock()" as try_lock_spec_alt with (
    \this this
    \prepost{q P g} this |-> R g q P
    \persist{th} current_thread th
    \pre{q'} token g q'
    \post{b}[Vbool b] if b then P ** locked g th q' else token g q').

  (* Obtain same specs from (Basic)Lockable. *)
  (** <<std::shared_mutex>> implements [BasicLockable] *)
  Definition T : Type := gname * mpred.

  #[global] Instance shared_mutex_basic_lockable : BasicLockable (T:=T) "std::shared_mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_lock := fun this => do_lock
  ; do_unlock := fun this => do_unlock }.

  cpp.spec "std::shared_mutex::lock()" as lock_spec with
  (\exact Reduce (lock_basic_lockable "std::shared_mutex" (λ q γP, R γP.1 q γP.2))).

  cpp.spec "std::shared_mutex::unlock()" as unlock_spec with
  (\exact Reduce (unlock_basic_lockable "std::shared_mutex" (λ q γP, R γP.1 q γP.2))).

  Definition do_try_lock (lk : gname * mpred) (Q : bool -> mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ q thr, current_thread thr ∗ token g q ∗
    ∀ b : bool,
    (if b then P ** locked g thr q else token g q) -∗ Q b.
  #[global] Arguments do_try_lock /.

  #[global,program] Instance shared_mutex_lockable : Lockable (T:=T) "std::shared_mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_try_lock := fun this => do_try_lock }.

  cpp.spec "std::shared_mutex::try_lock()" as try_lock_spec with
  (\exact Reduce (try_lock_lockable "std::mutex" (λ q γP, R γP.1 q γP.2))).

  Lemma lock_spec_entails_lock_spec_alt : lock_spec -|- lock_spec_alt.
  Proof.
    iSplit; iApply specify_mono; ework with br_erefl.
  Qed.

  Lemma unlock_spec_entails_unlock_spec_alt : unlock_spec -|- unlock_spec_alt.
  Proof.
    iSplit; iApply specify_mono; ework with br_erefl.
  Qed.

  Lemma try_lock_spec_entails_try_lock_spec_alt : try_lock_spec -|- try_lock_spec_alt.
  Proof.
    iSplit; iApply specify_mono; ework with br_erefl.
  Qed.
   *)
End with_cpp.
End shared_mutex.
