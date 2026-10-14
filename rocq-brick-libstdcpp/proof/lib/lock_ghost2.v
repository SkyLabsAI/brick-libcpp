Require Import iris.algebra.agree.
Require Import iris.algebra.frac.
Require Import iris.algebra.functions.
Require Import iris.algebra.gmap.
Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.
Require Import iris.algebra.lib.gmap_view.
Require Import iris.algebra.coPset.

Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Import linearity.

(**  Various ghost state constructions and laws for concurrency library specs and proofs. *)

Module mutex_set_G.
  Canonical Structure cmraR : cmra :=
    thread_idT -d> coPset_disjR.

  Class mutex_set_preG `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments mutex_set_preG {_ _} Σ : assert.

  (* Users of a mutex_set_map ghost state should assume a single instance for
    the entire C++ program. This can be done by using a single instance of
    [mutex_set_G] to fix [mutex_sets_name]. *)
  Class mutex_set_G `{Σ : cpp_logic} := {
    #[global] pre_G :: mutex_set_preG Σ;
    mutex_sets_name : iprop.gname;
  }.
  #[global] Arguments mutex_set_G {_ _} Σ : assert.
End mutex_set_G.

Module MutexSets.
  Import mutex_set_G.
  #[local] Existing Instances has_own has_upd has_valid.

  Definition my_mutexes `{Σ : cpp_logic, !mutex_set_G Σ}
      (th : thread_idT) (E : coPset_disj) : mpred :=
    own mutex_sets_name (discrete_fun_singleton th E : cmraR).

  (** The pool reserves the full set for each thread not yet registered. *)
  Definition reserve (M : gset thread_idT) : cmraR :=
    fun th => if decide (th ∈ M) then ε else CoPset ⊤.

  Definition mutex_set_map `{Σ : cpp_logic, !mutex_set_G Σ}
      (M : gset thread_idT) : mpred :=
    own mutex_sets_name (reserve M).

  Lemma alloc_mutex_set_map `{Σ : cpp_logic, !mutex_set_preG Σ} :
    ⊢ |==> ∃ _ : mutex_set_G Σ, mutex_set_map ∅.
  Proof.
    iMod (own_alloc (reserve ∅)) as (γ) "Hmap".
    { intros th. rewrite /reserve. case_decide; done. }
    iModIntro. iExists {| pre_G := _; mutex_sets_name := γ |}.
    iExact "Hmap".
  Qed.

  Section theory.
    Context `{Σ : cpp_logic, !mutex_set_G Σ}.

    #[global] Instance mutex_set_map_timeless M :
      Timeless (mutex_set_map M).
    Proof. rewrite /mutex_set_map. apply _. Qed.
    #[global] Instance my_mutexes_timeless th E :
      Timeless (my_mutexes th E).
    Proof. rewrite /my_mutexes. apply _. Qed.

    #[global] Instance mutex_set_map_WeaklyObjective M :
      WeaklyObjective (mutex_set_map M).
    Proof. rewrite /mutex_set_map. apply _. Qed.
    #[global] Instance my_mutexes_WeaklyObjective th E :
      WeaklyObjective (my_mutexes th E).
    Proof. rewrite /my_mutexes. apply _. Qed.
    #[global] Instance my_mutexes_objective th E :
      Objective (my_mutexes th E).
    Proof. rewrite /my_mutexes. apply _. Qed.

    Lemma my_mutexes_exclusive th (E1 E2 : coPset) :
      ~(E1 ## E2) ->
      my_mutexes th (CoPset E1) **
      my_mutexes th (CoPset E2) |-- False.
    Proof.
      rewrite /my_mutexes.
      iIntros (Hoverlap) "[H1 H2]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
      iPureIntro.
      specialize (Hvalid th).
      rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton in Hvalid.
      rewrite coPset_disj_valid_op in Hvalid.
      set_solver.
    Qed.

    (* does not need the update, but is implementation detail. *)
    Lemma mutex_sets_alloc_thread' T th :
      th ∉ T ->
      mutex_set_map T |--
        mutex_set_map (T ∪ {[th]}) ** my_mutexes th (CoPset ⊤).
    Proof.
      intros Hfresh.
      rewrite /mutex_set_map /my_mutexes -own_op.
      have Heq : reserve T ≡
          reserve (T ∪ {[th]}) ⋅ discrete_fun_singleton th (CoPset ⊤).
      { intros th'.
        rewrite discrete_fun_lookup_op.
        destruct (decide (th = th')) as [<-|Hne].
        - rewrite discrete_fun_lookup_singleton /reserve.
          rewrite decide_False; last done.
          rewrite decide_True; last set_solver.
          by rewrite left_id.
        - rewrite discrete_fun_lookup_singleton_ne; last done.
          rewrite right_id /reserve.
          destruct (decide (th' ∈ T)).
          + rewrite !decide_True; try set_solver.
          + rewrite !decide_False; try set_solver.
      }
      by rewrite Heq.
    Qed.

    Lemma mutex_sets_alloc_thread T th :
      th ∉ T ->
      mutex_set_map T |--
        (|==> mutex_set_map (T ∪ {[th]}) **
                my_mutexes th (CoPset ⊤)).
    Proof.
      iIntros (Hfresh) "Hmap". iModIntro.
      iApply (mutex_sets_alloc_thread' T th Hfresh with "Hmap").
    Qed.

    Lemma mutex_sets_free_thread T th :
      th ∈ T ->
      mutex_set_map T ** my_mutexes th (CoPset ⊤) |--
        mutex_set_map (T \ {[th]}).
    Proof.
      intros Hmember.
      rewrite /mutex_set_map /my_mutexes -own_op.
      have Heq : reserve T ⋅ discrete_fun_singleton th (CoPset ⊤) ≡
          reserve (T \ {[th]}).
      { intros th'.
        rewrite discrete_fun_lookup_op.
        destruct (decide (th = th')) as [<-|Hne].
        - rewrite discrete_fun_lookup_singleton /reserve.
          rewrite decide_True; last done.
          rewrite decide_False; last set_solver.
          by rewrite left_id.
        - rewrite discrete_fun_lookup_singleton_ne; last done.
          rewrite right_id /reserve.
          destruct (decide (th' ∈ T)).
          + rewrite !decide_True; try set_solver.
          + rewrite !decide_False; try set_solver.
      }
      by rewrite Heq.
    Qed.

    Lemma mutex_set_map_empty_no_my_mutexes th (N : namespace) :
      mutex_set_map ∅ ** my_mutexes th (CoPset (↑N)) |-- False.
    Proof.
      rewrite /mutex_set_map /my_mutexes.
      iIntros "[Hmap Hmy]".
      iDestruct (own_valid_2 with "Hmap Hmy") as %Hvalid.
      iPureIntro.
      specialize (Hvalid th).
      rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton /reserve in Hvalid.
      rewrite coPset_disj_valid_op in Hvalid.
      have Hnonempty := nclose_non_empty N.
      set_solver.
    Qed.

    Lemma my_mutexes_alloc_mutex_name th (E N : coPset) :
      N ⊆ E ->
      my_mutexes th (CoPset E) |--
        my_mutexes th (CoPset (E \ N)) ** my_mutexes th (CoPset N).
    Proof.
      intros Hsub.
      rewrite /my_mutexes -own_op discrete_fun_singleton_op.
      rewrite coPset_disj_union; last set_solver.
      rewrite difference_union_L.
      have -> : E ∪ N = E by set_solver.
      done.
    Qed.

    Lemma my_mutexes_split th (E1 E2 : coPset) :
      E1 ## E2 ->
      my_mutexes th (CoPset (E1 ∪ E2)) ⊣⊢
        my_mutexes th (CoPset E1) ** my_mutexes th (CoPset E2).
    Proof.
      intros Hdisjoint.
      rewrite /my_mutexes -own_op discrete_fun_singleton_op.
      by rewrite coPset_disj_union.
    Qed.

    Lemma my_mutexes_join_mutex_name th (E N : coPset) :
      N ⊆ E ->
      my_mutexes th (CoPset (E \ N)) ** my_mutexes th (CoPset N) |--
        my_mutexes th (CoPset E).
    Proof.
      intros Hsub.
      rewrite -my_mutexes_split; last set_solver.
      rewrite difference_union_L.
      have -> : E ∪ N = E by set_solver.
      done.
    Qed.

  End theory.

  (* an example that two threads can allocate the same namespace token. *)
  Lemma my_mutexes_alloc_eg : forall `{Σ : cpp_logic, !mutex_set_preG Σ}
      (th1 th2 : thread_idT) (N : coPset),
    th1 ≠ th2 ->
    ⊢ |==> ∃ _ : mutex_set_G Σ,
      my_mutexes th1 (CoPset N) **
      my_mutexes th2 (CoPset N) **
      (mutex_set_map {[th1; th2]} **
       my_mutexes th1 (CoPset (⊤ \ N)) **
       my_mutexes th2 (CoPset (⊤ \ N))).
  Proof.
    intros until N. intros Hneq.
    iMod alloc_mutex_set_map as (HG) "Hmap".
    iMod (mutex_sets_alloc_thread ∅ th1 ltac:(set_solver)
      with "Hmap") as "[Hmap Ht1]".
    iEval (rewrite left_id_L) in "Hmap".
    iMod (mutex_sets_alloc_thread {[th1]} th2 ltac:(set_solver)
      with "Hmap") as "[Hmap Ht2]".
    iDestruct (my_mutexes_alloc_mutex_name th1 ⊤ N ltac:(set_solver)
      with "Ht1") as "[Hr1 Hn1]".
    iDestruct (my_mutexes_alloc_mutex_name th2 ⊤ N ltac:(set_solver)
      with "Ht2") as "[Hr2 Hn2]".
    iModIntro. iExists HG. iFrame.
  Qed.

  #[global] Hint Opaque mutex_set_map my_mutexes : sl_opacity typeclass_instances.
End MutexSets.

(** Tracks a fraction. *)

Module MutexTokens.
  Canonical Structure cmraR : cmra := fracR.

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition token `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (q : Qp) : mpred :=
    own γ (q : cmraR).

  #[global] Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : Fractional (token γ).
  Proof.
    intros q1 q2. rewrite /token -own_op /=. done.
  Qed.

  #[global] Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  Proof. rewrite /token. apply _. Qed.

  #[global] Hint Opaque token : sl_opacity typeclass_instances.

  Section theory.
    Context `{Σ : cpp_logic, !G Σ}.

    #[local] Existing Instance mpred_BiAffine.

    Lemma token_valid γ q : token γ q |-- [| (q ≤ 1)%Qp |].
    Proof.
      rewrite /token. iIntros "H".
      iDestruct (own_valid with "H") as %Hvalid.
      iPureIntro. exact Hvalid.
    Qed.

    Lemma token_valid_2 γ q1 q2 :
      token γ q1 ** token γ q2 |-- [| (q1 + q2 ≤ 1)%Qp |].
    Proof. rewrite -fractional. apply token_valid. Qed.

    Lemma alloc : ⊢ |==> ∃ γ, token γ 1.
    Proof.
      iMod (own_alloc (1%Qp : cmraR)) as (γ) "H"; first done.
      iModIntro. iExists γ. iExact "H".
    Qed.
  End theory.
End MutexTokens.

(** Authoritative and exclusive fragment ownership of an optional thread ID
    and the exact token share deposited by that thread. *)
Module OwnerTid.
  Canonical Structure cmraR : cmra :=
    excl_authR (optionO (prodO thread_idTO (leibnizO cQp.t))).

  Class G `{Σ : cpp_logic} := {
    #[local] has_own :: HasOwn (iPropI _Σ) cmraR;
    #[local] has_upd :: HasOwnUpd (iPropI _Σ) cmraR;
    #[local] has_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition owner_tid_auth `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (o : option (thread_idT * cQp.t)) : mpred :=
    own γ ((●E o) : cmraR).
  Definition owner_tid_frag `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (o : option (thread_idT * cQp.t)) : mpred :=
    own γ ((◯E o) : cmraR).

  #[global] Instance owner_tid_auth_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_auth γ o).
  Proof. rewrite /owner_tid_auth. apply _. Qed.
  #[global] Instance owner_tid_frag_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_frag γ o).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_tid_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_tid_frag γ).
  Proof.
    intros o1 o2. rewrite /owner_tid_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid. rewrite excl_auth_frag_op_valid. done.
  Qed.

  #[global] Instance owner_tid_auth_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_auth γ o).
  Proof. rewrite /owner_tid_auth. apply _. Qed.
  #[global] Instance owner_tid_frag_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_frag γ o).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_agree `{Σ : cpp_logic, !G Σ} γ o1 o2 :
    Observe2 [| o1 = o2 |] (owner_tid_auth γ o1) (owner_tid_frag γ o2).
  Proof.
    apply observe_2_intro_only_provable.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "A F".
    iDestruct (own_valid_2 with "A F") as %HV.
    iPureIntro. apply leibniz_equiv, excl_auth_agree, HV.
  Qed.

  Lemma alloc `{Σ : cpp_logic, !G Σ} o :
    ⊢ |==> ∃ γ, owner_tid_auth γ o ** owner_tid_frag γ o.
  Proof.
    iMod (own_alloc ((●E o ⋅ ◯E o) : cmraR)) as (γ) "H".
    { apply excl_auth_valid. }
    iModIntro. iExists γ.
    rewrite /owner_tid_auth /owner_tid_frag -own_op. iExact "H".
  Qed.

  Lemma owner_update `{Σ : cpp_logic, !G Σ} γ oa ofrag o' :
    owner_tid_auth γ oa ** owner_tid_frag γ ofrag |--
      (|==> owner_tid_auth γ o' ** owner_tid_frag γ o').
  Proof.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "[A F]".
    iMod (own_update_2 with "A F") as "[$ $]";
      first apply (excl_auth_update _ _ o').
    done.
  Qed.

  #[global] Hint Opaque owner_tid_auth owner_tid_frag : sl_opacity typeclass_instances.
End OwnerTid.
