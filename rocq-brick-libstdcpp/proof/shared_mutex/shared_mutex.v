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

  Definition reader_locked `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (th : thread_idT) (q : Qp) : mpred :=
    own γ.(phys_state_gname) (◯ {[ th := q ]}).

  (** Adapted from https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lib/rw_spin_lock.v?ref_type=heads

    Allows to prove writer_writer_exclusive and writer_reader_exclusive.
    Unlike them, we can't just use ∅ for the reader map, because when the
    writer unlocks, the cinv stores its `not_locked γ th`, but `th` is existentially
    quanified in cinv and it needs some way to recover that `th` matches with
    itself. Note that we still lose writer_reader_exclusiveness for the same,
    thread, but that should be fine with the current cinv.
  *)
  Definition locked `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (th : thread_idT) : mpred :=
    own γ.(phys_state_gname) (●{# 3/4} {[ th := 1%Qp ]}).

  Local Lemma writer_writer_exclusive `{Σ : cpp_logic, !lockedG Σ}
      γ th1 th2 :
    locked γ th1 -∗ locked γ th2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "%Hvalid".
    exfalso.
    rewrite
      auth_auth_dfrac_op_valid
      dfrac_op_own
      dfrac_valid_own in Hvalid.
    by destruct Hvalid as [? _].
  Qed.

  Local Lemma reader_writer_exclusive `{Σ : cpp_logic, !lockedG Σ}
      γ th1 th2 q:
    th1 <> th2 ->
    reader_locked γ th1 q -∗ locked γ th2 -∗ False.
  Proof.
    iIntros (Hneq) "H1 H2".
    iDestruct (own_valid_2 with "H2 H1") as "%Hvalid".
    exfalso.
    apply auth_both_dfrac_valid in Hvalid as (_ & Hvalid & _).
    generalize (Hvalid 0)=> H.
    apply singleton_includedN_l in H as (? & ? & ?).
    rewrite lookup_singleton in H.
    destruct decide in H; try done.
    inv H.
  Qed.

  Definition used_threads
      `{Σ : cpp_logic, !lockedG Σ}
      (γ : gname) (s : gset thread_idT) : mpred :=
      own γ.(login_gname) (● GSet s).

  Definition users
      `{Σ : cpp_logic, !lockedG Σ}
      (γ : gname) (ths : gset thread_idT) : mpred :=
    own γ.(login_gname) (◯ GSet ths).
  #[global] Hint Opaque users : sl_opacity typeclass_instances.

  (* not_locked is the handle to call lock functions *)
  Abbreviation not_locked γ th :=
    (users γ {[ th ]}).

  Context `{Σ : cpp_logic}.
  Context `{!lockedG Σ}.
  Context `{!HasStdThreads Σ}.

  #[global] Instance
      locked_WeaklyObjective γ thr :
      WeaklyObjective (PROP := iPropI _) (locked γ thr).
  Proof. (* locked.unlock. *) apply _. Qed.

  #[global] Hint Opaque locked : sl_opacity typeclass_instances.

  #[global] Instance
      reader_locked_WeaklyObjective γ thr n :
      WeaklyObjective (PROP := iPropI _) (reader_locked γ thr n).
  Proof. (* locked.unlock. *) apply _. Qed.

  #[global] Hint Opaque reader_locked : sl_opacity typeclass_instances.


  Lemma not_locked_unique g th :
    not_locked g th ** not_locked g th |-- False.
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
    (|==> used_threads g ({[ th ]} ∪ s) ** not_locked g th).
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
    used_threads g ({[ th ]} ∪ s) ** not_locked g th |--
    (|==> used_threads g s).
  Proof.
    rewrite /users /used_threads.

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

  Lemma used_threads_empty_no_not_locked g th :
    used_threads g ∅ ** not_locked g th |-- False.
  Proof.
    rewrite /users /used_threads.
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

  Definition smutex_N : namespace :=
    nroot .@@ "std" .@@ "shared_mutex" .@ "raw_inv".

  Section with_Qcanon.
    Import Qcanon.

    Definition oqp_to_qc (oqp : option Qp) : Qc :=
      match oqp with
      | Some qP => Qp_to_Qc qP
      | None => 0%Qc
      end.

    Definition smutex_inv γ (P : Qp -> mpred) : mpred :=
      ∃ (oqP : option Qp) ths borrow_map,
        match oqP with
        | Some qP => P qP
        | None => emp
        end **
        (* the set of borrowers *)
        users γ ths **
        (* writer mode: cinv keeps ●{# 1/4} of the borrow map and the frac so
            writer can't call shared_unlock(). writer has ●{# 3/4}.
          reader mode: cinv keeps the full borrow map, readers has the fracs. *)
        ((
          own γ.(phys_state_gname) (●{# 1/4} borrow_map) ∗
          own γ.(phys_state_gname) (◯ borrow_map) ∧
          ∃ th, [| borrow_map = {[ th := 1%Qp ]} |]
        ) ∨
        own γ.(phys_state_gname) (● borrow_map)) **
        (* the permission borrowed and the permission left in the inv sums to 1 *)
        [| map_fold (λ _ qi q, (Qp_to_Qc qi) + q) (oqp_to_qc oqP) borrow_map = 1%Qc |] **
        (* all borrowers have to turn in their `not_locked` handle *)
        [| ∀ th, th ∈ ths ↔ th ∈ dom borrow_map |].
  End with_Qcanon.

  (** Convention:
    qi: fraction of the invariant
    qP: fraction of P
    TODO: still relevant?
  *)

  Local Lemma writer_reader_excl g th1 th2 qP :
    th1 ≠ th2 ->
    reader_locked g th1 qP ** locked g th2 |-- False.
  Proof.
    iIntros (?) "[H1 H2]".
    iDestruct (reader_writer_exclusive with "H1 H2") as %[]; done.
  Qed.

  Local Lemma writer_writer_excl g th1 th2 :
    locked g th1 ** locked g th2 |-- False.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (writer_writer_exclusive with "H1 H2") as %[]; done.
  Qed.

  (** Fractional ownership of a <<std::shared_mutex>> guarding the predicate <<P>>. *)
  Definition R γ (q : cQp.t) (P : Qp -> mpred) : Rep :=
    structR "std::shared_mutex" q **
    (* should also have ownership of the underlying fields *)
    pureR (cinv smutex_N γ.(inv_gname) (smutex_inv γ P) **
           cinv_own γ.(inv_gname) q).
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr="std::shared_mutex")] derive R.
  #[global] Declare Instance R_learnable : forall {σ : genv},
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
    \pre not_locked g thr
    \post P 1%Qp ** locked g thr).

  cpp.spec "std::shared_mutex::try_lock()" as try_lock_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre not_locked g thr
    \post{b}[Vbool b] if b then P 1%Qp ** locked g thr else not_locked g thr).

  cpp.spec "std::shared_mutex::unlock()" as unlock_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre locked g thr
    \pre ▷ P 1%Qp
    \post not_locked g thr).

  cpp.spec "std::shared_mutex::lock_shared()" as lock_shared_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre not_locked g thr
    \post ∃ qP, P qP ** reader_locked g thr qP).

  cpp.spec "std::shared_mutex::try_lock_shared()" as try_lock_shared_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre not_locked g thr
    \post{b}[Vbool b] if b then ∃ qP, P qP ** reader_locked g thr qP else not_locked g thr).

  cpp.spec "std::shared_mutex::unlock_shared()" as unlock_shared_spec_alt with (
    \this this
    \prepost{qi P g} this |-> R g qi P
    \persist{thr} current_thread thr
    \pre{qP} reader_locked g thr qP
    \pre ▷P qP
    \post not_locked g thr).

  (** Safety Properties (we model violation of these properties as stuckness):
    1. a thread calling lock() or shared_lock() twice should fail.
      This is prevented by having a unique `not_locked`, and turn in not_locked in the inv.
    2. `lock(); ~shared_mutex()` should fail.
      Assume we have `used_threads g s`.
      dtor requires s=∅, but `lock()` puts the unique `not_locked γ th` in inv, so we
      can't deallocate that piece, therefore th ∈ s.
    3. `lock(); unlock_shared()` should fail.
      This is prevented because locked can't be transformed into reader_locked,
      and writer is not given one.
  *)

  Definition do_lock (lk : gname * (Qp -> mpred)) (K: mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ thr, current_thread thr ∗ not_locked g thr ∗
               (* TODO readd *)
               (* ▷ *)
               (locked g thr ** P 1%Qp -* K).
  #[global] Arguments do_lock /.

  Definition do_unlock (lk : gname * (Qp -> mpred)) (Q : mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ thr, current_thread thr ** locked g thr ** ▷P 1%Qp **
    (* TODO readd *)
    (* ▷ *)
    (not_locked g thr -* Q).
  #[global] Arguments do_unlock /.

  (* Obtain same specs from (Basic)Lockable. *)
  (** <<std::shared_mutex>> implements [BasicLockable] *)
  Definition T : Type := gname * (Qp -> mpred).

  #[global] Instance shared_mutex_basic_lockable : BasicLockable (T:=T) "std::shared_mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_lock := fun this => do_lock
  ; do_unlock := fun this => do_unlock }.

  cpp.spec "std::shared_mutex::lock()" as lock_spec with
  (\exact Reduce (lock_basic_lockable "std::shared_mutex" (λ q γP, R γP.1 q γP.2))).

  cpp.spec "std::shared_mutex::unlock()" as unlock_spec with
  (\exact Reduce (unlock_basic_lockable "std::shared_mutex" (λ q γP, R γP.1 q γP.2))).

  Definition do_try_lock (lk : gname * (Qp -> mpred)) (Q : bool -> mpred) : mpred :=
    let g := lk.1 in
    let P := lk.2 in
    ∃ thr, current_thread thr ∗ not_locked g thr ∗
    ∀ b : bool,
    (if b then P 1%Qp ** locked g thr else not_locked g thr) -∗ Q b.
  #[global] Arguments do_try_lock /.

  #[global,program] Instance shared_mutex_lockable : Lockable (T:=T) "std::shared_mutex" (λ q γP, R γP.1 q γP.2) :=
  { do_try_lock := fun this => do_try_lock }.

  cpp.spec "std::shared_mutex::try_lock()" as try_lock_spec with
  (\exact Reduce (try_lock_lockable "std::shared_mutex" (λ q γP, R γP.1 q γP.2))).

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
End with_cpp.
End shared_mutex.
