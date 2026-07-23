Require Import iris.algebra.gset.
Require Import iris.algebra.auth.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Section lock_ghost.

  Canonical Structure lock_ghostUR : ucmra :=
    gset_disjR thread_idTO.
  Canonical Structure lock_cmraR := authR lock_ghostUR.

  Class lockG `{Σ : cpp_logic} := {
    #[global] has_lock :: HasOwn (iPropI _Σ) lock_cmraR;
    #[global] has_lock_upd :: HasOwnUpd (iPropI _Σ) lock_cmraR;
    #[global] has_lock_valid :: HasOwnValid (iPropI _Σ) lock_cmraR;
  }.
  #[global] Arguments lockG {_ _} Σ : assert.

  Definition used_threads `{Σ : cpp_logic, !HasOwn (iPropI _Σ) lock_cmraR}
      (γ : iprop.gname) (s : gset thread_idT) : mpred :=
    own γ (● GSet s).
  #[global] Hint Opaque used_threads : sl_opacity.

  Definition users `{Σ : cpp_logic, !HasOwn (iPropI _Σ) lock_cmraR}
      (γ : iprop.gname) (ths : gset thread_idT) : mpred :=
    own γ (◯ GSet ths).
  #[global] Hint Opaque users : sl_opacity typeclass_instances.

  (* not_locked is the handle to call lock functions *)
  Definition not_locked `{Σ : cpp_logic, !HasOwn (iPropI _Σ) lock_cmraR}
      (γ : iprop.gname) (th : thread_idT) : mpred :=
    users γ {[ th ]}.
  #[global] Hint Opaque not_locked : sl_opacity.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{!lockG Σ}.

    Lemma not_locked_unique g th :
      not_locked g th ** not_locked g th |-- False.
    Proof using Type*.
      rewrite /not_locked.
      iIntros "[A B]".
      iDestruct (own_valid_2 with "A B") as "%".
      rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in H.
      set_solver.
    Qed.

    (* TODO rename to use_thread *)
    Lemma login th g s :
      th ∉ s ->
      used_threads g s |--
      (|==> used_threads g ({[ th ]} ∪ s) ** not_locked g th).
    Proof using Type*.
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
    Proof using Type*.
      rewrite /not_locked /users /used_threads.
      intros Hni.
      iIntros "[A B]".
      iCombine "A" "B" as "A".
      iMod (own_update with "A") as "?"; last by iFrame.
      apply (auth_update_dealloc _ _ (GSet s)).
      rewrite -gset_disj_union; last set_solver.
      apply gset_disj_dealloc_empty_local_update.
    Qed.

    Lemma used_threads_empty_no_not_locked g th :
      used_threads g ∅ ** not_locked g th |-- False.
    Proof using Type*.
      rewrite /not_locked /users /used_threads.
      iIntros "[A B]".
      iDestruct (own_valid_2 with "A B") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid.
      destruct Hvalid as [Hvalid _].
      rewrite gset_disj_included in Hvalid. set_solver.
    Qed.
  End with_cpp.

End lock_ghost.
