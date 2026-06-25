Require Import iris.algebra.gset.

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

  Canonical Structure lock_ghostUR : ucmra :=
    gset_disjR thread_idTO.
  Canonical Structure lock_cmraR := authR lock_ghostUR.

  (* maps th:thread_idT to the fraction of permission thaborrowed. *)
  Canonical Structure phys_stateUR := authR (gmapR thread_idT Qp).


  Class lockedG `{Σ : cpp_logic} := {
    #[local] has_locked :: HasOwn (iPropI _Σ) lock_cmraR;
    #[local] has_locked_upd :: HasOwnUpd (iPropI _Σ) lock_cmraR;
    #[local] has_locked_valid :: HasOwnValid (iPropI _Σ) lock_cmraR;

    #[local] has_phys_state :: HasOwn (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_upd :: HasOwnUpd (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_valid :: HasOwnValid (iPropI _Σ) phys_stateUR;
  }.

  #[global] Arguments lockedG {_ _} Σ : assert.

  Record gname : Set := MkGname
  { phys_state_gname : iprop.gname;
    login_gname : iprop.gname;
    inv_gname : iprop.gname;
  }.

  Definition borrow `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (th : thread_idT) (q : Qp) : mpred :=
    own γ.(phys_state_gname) (◯ {[ th := q ]}).

  Definition writer_borrow `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (th : thread_idT) : mpred :=
    borrow γ th 1%Qp.

  Definition borrow_state `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (borrowers : gmap thread_idT Qp) : mpred :=
    own γ.(phys_state_gname) (● borrowers).

  Definition used_threads
      `{Σ : cpp_logic, !lockedG Σ, !HasStdThreads Σ}
      (γ : gname) (s : gset thread_idT) : mpred :=
      own γ.(login_gname) (● GSet s).

  (* user is the handle to call lock functions *)
  Definition user `{Σ : cpp_logic, !lockedG Σ}
      (γ : gname) (th : thread_idT) : mpred :=
    own γ.(login_gname) (◯ GSet {[ th ]}).
  
  Context `{Σ : cpp_logic}.
  Context `{!lockedG Σ}.
  Context `{!HasStdThreads Σ}.
  
  #[global] Instance
      writer_borrow_WeaklyObjective γ thr :
      WeaklyObjective (PROP := iPropI _) (writer_borrow γ thr).
  Proof. (* locked.unlock. *) apply _. Qed.

  #[global] Instance
      reader_borrow_WeaklyObjective γ thr n :
      WeaklyObjective (PROP := iPropI _) (borrow γ thr n).
  Proof. (* locked.unlock. *) apply _. Qed.


  Lemma user_unique g th :
    user g th ** user g th |-- False.
  Proof.
    (* rewrite locked.unlock. *)
    iIntros "[A B]".
    iDestruct (own_valid_2 with "A B") as "%".
    rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in H.
    set_solver.
  Qed.

  Lemma login th g s :
    th ∉ s ->
    used_threads g s |--
    |==> used_threads g ({[ th ]} ∪ s) ** user g th.
  Proof.
    intros Hni.
    iIntros "A".
    iMod (own_update with "A") as "[● $]"; last iModIntro.
    {
      rewrite cmra_comm.
      apply (auth_update_alloc _ (GSet ({[th]} ∪ s)) (GSet {[th]})).
      apply gset_disj_alloc_empty_local_update. set_solver. 
    }
    by iFrame.
  Qed.

  Lemma logout th g s :
    th ∉ s ->
    used_threads g ({[ th ]} ∪ s) ** user g th |--
    |==> used_threads g s.
  Proof.
    intros Hni.

    iIntros "[A B]".
    iCombine "A" "B" as "A".
    iMod (own_update with "A") as "?".
    {
      apply (auth_update_dealloc _ _ (GSet s)).
      rewrite -gset_disj_union; last set_solver.
      apply gset_disj_dealloc_empty_local_update.
    }
    by iFrame.
  Qed.

  Lemma used_threads_empty_no_user g th :
    used_threads g ∅ ** user g th |-- False.
  Proof.
    rewrite /user /used_threads.
    iIntros "[A B]".
    iDestruct (own_valid_2 with "A B") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hvalid _].
    rewrite gset_disj_included in Hvalid. set_solver.
  Qed.

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

  Context `{MOD : source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  Definition smutex_N : namespace :=
    nroot .@@ "std" .@@ "shared_mutex" .@ "raw_inv".

  Definition users
      (γ : gname) (ths : gset thread_idT) : mpred :=
    own γ.(login_gname) (◯ GSet ths).
  
  Definition smutex_inv γ (P : Qp -> mpred) : mpred :=
    ∃ qP ths borrow_map,
      P qP **
      (* the set of borrowers *)
      users γ ths **
      borrow_state γ borrow_map **
      (* the permission borrowed and the permission left in the inv sums to 1 *)
      [| map_fold (λ _ qi q, Qp.add qi q) qP borrow_map = 1%Qp |] **
      (* all borrowers have to turn in their `user` handle *)
      [| ∀ th, th ∈ ths ↔ th ∈ dom borrow_map |].


  (** Convention:
    qi: fraction of the invariant
    qP: fraction of P 
  *)
  Definition reader_locked (γ : gname) (th : thread_idT) qi qP : mpred :=
    borrow γ th qP ∗ cinv_own γ.(inv_gname) qi.

  (* (writer) locked is just reader_locked with full permission *)
  Definition locked (γ : gname) (th : thread_idT) qi : mpred :=
    reader_locked γ th qi 1%Qp.
  
  Definition not_locked (γ : gname) (th : thread_idT) qi : mpred :=
    user γ th ** cinv_own γ.(inv_gname) qi.

  (* this does not hold! *)
  Lemma reader_writer_excl g th1 th2 qir qiw qP :
    reader_locked g th1 qir qP ** locked g th2 qiw |-- False.
  Proof.
    iIntros "[[H1 _] [H2 _]]".
    iCombine "H1" "H2" as "H".
  Abort.

  (* FIXME why does this not type check? *)
  (* Definition R γ (q : cQp.t) (P : Qp -> mpred) : Rep :=
    type_ptrR "std::shared_mutex" **
    cinv smutex_N γ.(inv_gname) (smutex_inv γ P) **
    (* if we have cinv_own, is some RA redundant? *)
    cinv_own γ.(inv_gname) q. *)
    
  (** Fractional ownership of a <<std::shared_mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> (Qp -> mpred) -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr="std::shared_mutex")] derive R.
  #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

  cpp.spec "std::shared_mutex::shared_mutex()" as ctor_spec with (
    \this this
    \pre{P} ▷P 1%Qp
    \post Exists g, this |-> R g 1$m P ** used_threads g ∅).

  cpp.spec "std::shared_mutex::~shared_mutex()" as dtor_spec with (
    \this this
    (** the "user" set being ∅ enforces that there is no reader or write *)
    \pre{g P} this |-> R g 1$m P ** used_threads g ∅
    \post P 1%Qp).

  (* "Inline" version of these specs. *)
  cpp.spec "std::shared_mutex::lock()" as lock_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre not_locked g thr qi
    \post P 1%Qp ** locked g thr qi).

  cpp.spec "std::shared_mutex::unlock()" as unlock_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre locked g thr qi
    \pre ▷ P 1%Qp
    \post not_locked g thr qi).

  cpp.spec "std::shared_mutex::lock_shared()" as lock_shared_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre not_locked g thr qi
    \post ∃ qP, P qP ** reader_locked g thr qi qP).

  cpp.spec "std::shared_mutex::unlock_shared()" as unlock_shared_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre locked g thr qi
    \pre ▷P 1%Qp
    \post not_locked g thr qi).

  (** Safety Properties:
    1. a thread calling lock() or shared_lock() twice should fail.
      This is prevented by having a unique `user`, and turn in user in the inv.
    2. `lock(); ~shared_mutex()` should fail.
      Assume we have `used_threads g s`.
      dtor requires s=∅, but `lock()` puts the unique `user γ th` in inv, so we
      can't deallocate that piece, therefore th ∈ s.
  *)

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
