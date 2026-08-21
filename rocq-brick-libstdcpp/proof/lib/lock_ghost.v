Require Import iris.algebra.gset.
Require Import iris.algebra.auth.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Import linearity.

Canonical Structure lock_ghostUR : ucmra :=
  gset_disjR thread_idTO.
Canonical Structure lock_cmraR := authR lock_ghostUR.

Class lockG `{Σ : cpp_logic} := {
  #[local] has_lock :: HasOwn (iPropI _Σ) lock_cmraR;
  #[local] has_lock_upd :: HasOwnUpd (iPropI _Σ) lock_cmraR;
  #[local] has_lock_valid :: HasOwnValid (iPropI _Σ) lock_cmraR;
}.
#[global] Arguments lockG {_ _} Σ : assert.

sl.lock
Definition used_threads `{Σ : cpp_logic, !lockG Σ}
    (γ : iprop.gname) (s : gset thread_idT) : mpred :=
  own γ (● GSet s).
#[only(timeless)] derive used_threads.

sl.lock
Definition users `{Σ : cpp_logic, !lockG Σ}
    (γ : iprop.gname) (ths : gset thread_idT) : mpred :=
  own γ (◯ GSet ths).
#[only(timeless)] derive users.

(* not_locked is the handle to call lock functions *)
Abbreviation not_locked γ th := (users γ {[ th ]}).

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{!lockG Σ}.

  #[global] Instance
    locked_WeaklyObjective γ thr :
    WeaklyObjective (PROP := iPropI _) (users γ thr).
  Proof. rewrite users.unlock. apply _. Qed.

  (** *** ghost state set agreement observations *)
  #[global] Instance used_threads_users_agree g ths1 ths2 :
    Observe2 [| ths2 ⊆ ths1 |] (used_threads g ths1) (users g ths2).
  Proof.
    apply observe_2_intro_only_provable; iIntros "A B".
    rewrite users.unlock used_threads.unlock.
    by iDestruct (own_valid_2 with "A B") as
      %[Hvalid%gset_disj_included _]%auth_both_valid_discrete.
  Qed.

  #[global] Instance users_disjoint g ths1 ths2 :
    Observe2 [| ths1 ## ths2 |] (users g ths1) (users g ths2).
  Proof.
    apply observe_2_intro_only_provable; iIntros "A B"; rewrite users.unlock.
    iDestruct (own_valid_2 with "A B") as %Hv.
    by rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in Hv.
  Qed.

  (** *** ghost state set agreement observations: corollaries *)
  Lemma used_threads_empty_no_not_locked g th :
    used_threads g ∅ ** not_locked g th |-- False.
  Proof.
    iIntros "[A B]". iDestruct (observe_2_elim_pure with "A B") as %?.
    set_solver.
  Qed.

  Lemma not_locked_unique g th :
    not_locked g th ** not_locked g th |-- False.
  Proof.
    iIntros "[A B]". iDestruct (observe_2_elim_pure with "A B") as %?.
    set_solver.
  Qed.

  (** *** ghost state manipulation:
  borrow [not_locked] from [used_threads] and back. *)
  (* TODO rename to use_thread *)
  Lemma login th g s :
    th ∉ s ->
    used_threads g s |--
    (|==> used_threads g (s ∪ {[ th ]}) ** not_locked g th).
  Proof.
    rewrite users.unlock used_threads.unlock.
    iIntros (Hni) "A".
    iMod (own_update with "A") as "[● $]"; last by iModIntro; iFrame.
    rewrite (comm op) (comm_L union).
    apply (auth_update_alloc _ (GSet ({[ th ]} ∪ s)) (GSet {[th]})).
    apply gset_disj_alloc_empty_local_update. set_solver.
  Qed.

  Lemma logout th g s :
    th ∉ s ->
    used_threads g (s ∪ {[ th ]}) ** not_locked g th |--
    (|==> used_threads g s).
  Proof.
    rewrite users.unlock used_threads.unlock.
    iIntros (Hni) "[A B]".
    iApply (own_update_2 with "A B").
    apply (auth_update_dealloc _ _ (GSet s)).
    rewrite (comm_L (∪)) -gset_disj_union; last set_solver.
    apply gset_disj_dealloc_empty_local_update.
  Qed.
End with_cpp.
