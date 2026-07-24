Require Import iris.algebra.gset.
Require Import iris.algebra.auth.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

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

  Lemma not_locked_unique g th :
    not_locked g th ** not_locked g th |-- False.
  Proof.
    rewrite users.unlock.
    iIntros "[A B]".
    iDestruct (own_valid_2 with "A B") as %Hv.
    rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in Hv.
    set_solver.
  Qed.

  (* TODO rename to use_thread *)
  Lemma login th g s :
    th ∉ s ->
    used_threads g s |--
    (|==> used_threads g ({[ th ]} ∪ s) ** not_locked g th).
  Proof.
    rewrite users.unlock used_threads.unlock.
    intros Hni.
    iIntros "A".
    iMod (own_update with "A") as "[● $]"; last by iModIntro; iFrame.
    rewrite cmra_comm.
    apply (auth_update_alloc _ (GSet ({[th]} ∪ s)) (GSet {[th]})).
    apply gset_disj_alloc_empty_local_update. set_solver.
  Qed.

  Lemma logout th g s :
    th ∉ s ->
    used_threads g ({[ th ]} ∪ s) ** not_locked g th |--
    (|==> used_threads g s).
  Proof.
    rewrite users.unlock used_threads.unlock.
    intros Hni.
    iIntros "[A B]".
    iApply (own_update_2 with "A B").
    apply (auth_update_dealloc _ _ (GSet s)).
    rewrite -gset_disj_union; last set_solver.
    apply gset_disj_dealloc_empty_local_update.
  Qed.

  Lemma used_threads_empty_no_not_locked g th :
    used_threads g ∅ ** not_locked g th |-- False.
  Proof.
    rewrite users.unlock used_threads.unlock.
    iIntros "[A B]".
    iDestruct (own_valid_2 with "A B") as
      %[Hvalid%gset_disj_included _]%auth_both_valid_discrete.
    set_solver.
  Qed.
End with_cpp.
