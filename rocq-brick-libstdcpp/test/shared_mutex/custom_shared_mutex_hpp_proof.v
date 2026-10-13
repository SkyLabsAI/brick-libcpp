Require Import iris.algebra.coPset.
Require Import iris.algebra.lib.gmap_view.
Require Import iris.algebra.agree.
Require Import iris.algebra.frac.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.atomic.spec.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.shared_mutex.shared_mutex.
Require Import skylabs.brick.libstdcpp.test.shared_mutex.custom_shared_mutex_hpp.

NES.Open std.atomic.

Import linearity.
#[local] Existing Instance mpred_BiAffine.

Module CustomSharedMutexPreds <: SHARED_MUTEX_PREDS.
  Definition class_name : name := "MySharedMutex"%cpp_name.
  Definition cpp_ty : type := Tnamed class_name.
  #[global] Arguments cpp_ty /.
  #[global] Arguments class_name /.

  (** The invariant holds the auth piece of [holdersR], and each reader/writer
      holds a frac. The map is partial, so only active readers & writers are in
      the map. An [entry] of holdersR stores (qt, o_qP), where qt is the
      caller's token fraction and o_qP is the optional resource fraction:
      (Some qP) represents a reader that borrows [P qP] and [None] represents
      a writer.

      [reader_map] encodes the fractions when all threads are readers.

      It might be possible to make [holdersR] a map to reader_map and encode
      a writer as having a fraction of [1], but we choose to explicitly make
      the writer entry (None) to be distinct with reader entry (Some qP) on
      the type level. *)
  Definition reader_map := gmap thread_idT (cQp.t * Qp).
  Definition entry := (cQp.t * option Qp)%type.
  Canonical Structure holdersR : cmra :=
    gmap_viewR thread_idT (agreeR (leibnizO entry)).

  Record mutex_gname : Set := MkGname {
    token_gname : iprop.gname;
    share_gname : iprop.gname;
    holders_gname : iprop.gname;
    cinv_gname : iprop.gname;
    inv_namespace : namespace;
  }.
  Definition gname : Set := mutex_gname.
  Definition smutex_inv_namespace (g : gname) := g.(inv_namespace).

  Class stateG `{Σ : cpp_logic} := {
    #[local] holders_own :: HasOwn (iPropI _Σ) holdersR;
    #[local] holders_upd :: HasOwnUpd (iPropI _Σ) holdersR;
    #[local] holders_valid :: HasOwnValid (iPropI _Σ) holdersR;
  }.
  Definition G := @stateG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance state_G `{Σ : cpp_logic} (H : G Σ) : @stateG _ _ Σ := H.

  Definition token `{Σ : cpp_logic, !G Σ} (g : gname) (q : cQp.t) : mpred :=
    own g.(token_gname) (q : fracR).
  (** [P qP] is always accompanied with [share g qP]: initially the invariant
    keeps [share 1 ** P 1]; when a thread borrows [P qP], it also borrows
    [share g qP]. This allows to prove writer-writer or writer-reader
    exclusivity. *)
  Definition share `{Σ : cpp_logic, !G Σ} (g : gname) (q : Qp) : mpred :=
    own g.(share_gname) (q : fracR).
  Definition authority `{Σ : cpp_logic, !G Σ}
      (g : gname) (M : gmap thread_idT entry) : mpred :=
    own g.(holders_gname)
      (gmap_view_auth (DfracOwn 1) (to_agree (A := leibnizO entry) <$> M) : holdersR).
  Definition holder `{Σ : cpp_logic, !G Σ}
      (g : gname) (th : thread_idT) (e : entry) : mpred :=
    own g.(holders_gname)
      (gmap_view_frag th (DfracOwn 1) (to_agree (A := leibnizO entry) e) : holdersR).

  Definition not_locked `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    token g qt ** MutexSets.my_mutexes th
      (CoPset $ ↑smutex_inv_namespace g).
  Definition locked `{Σ : cpp_logic, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    holder g th (qt, None) ** share g 1.
  Definition reader_locked `{Σ : cpp_logic, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) (qP : Qp) : mpred :=
    holder g th (qt, Some qP) ** share g qP.

  #[global] Instance token_fractional `{Σ : cpp_logic, !G Σ} g :
      CFractional (token g).
  Proof. intros q1 q2. rewrite /token cQp.frac_add -frac_op own_op. done. Qed.
  #[global] Instance token_timeless `{Σ : cpp_logic, !G Σ} g q :
      Timeless (token g q).
  Proof. rewrite /token. apply _. Qed.
  #[global] Instance share_fractional `{Σ : cpp_logic, !G Σ} g :
      Fractional (share g).
  Proof. intros q1 q2. rewrite /share -frac_op own_op. done. Qed.
  #[global] Instance authority_timeless `{Σ : cpp_logic, !G Σ} g M :
      Timeless (authority g M).
  Proof. rewrite /authority. apply _. Qed.
  #[global] Instance holder_timeless `{Σ : cpp_logic, !G Σ} g th e :
      Timeless (holder g th e).
  Proof. rewrite /holder. apply _. Qed.
  #[global] Instance share_timeless `{Σ : cpp_logic, !G Σ} g q :
      Timeless (share g q).
  Proof. rewrite /share. apply _. Qed.

  Section ghost_laws.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma full_share_exclusive g q : share g 1 ** share g q |-- False.
    Proof.
      rewrite /share. iIntros "[A B]".
      iDestruct (own_valid_2 with "A B") as %Hvalid.
      iPureIntro. move: Hvalid. rewrite frac_op frac_valid.
      exact (Qp.not_add_le_l 1 q).
    Qed.

    Lemma full_token_exclusive g q : token g 1$m ** token g q |-- False.
    Proof.
      rewrite /token. iIntros "[A B]".
      iDestruct (own_valid_2 with "A B") as %Hvalid.
      iPureIntro. move: Hvalid. rewrite frac_op frac_valid.
      exact (Qp.not_add_le_l 1 q).
    Qed.

    Lemma holder_lookup g M th e :
      authority g M ** holder g th e |-- [| M !! th = Some e |].
    Proof.
      rewrite /authority /holder. iIntros "[A F]".
      iDestruct (own_valid_2 with "A F") as %Hvalid.
      apply gmap_view_both_valid in Hvalid as (_ & _ & Heq).
      rewrite lookup_fmap in Heq.
      destruct (M !! th) as [e'|] eqn:Hlookup; rewrite Hlookup /= in Heq; last inversion Heq.
      apply Some_equiv_inj, to_agree_inj, leibniz_equiv in Heq.
      subst e'. done.
    Qed.

    Lemma holder_insert g M th e :
      M !! th = None ->
      authority g M |-- (|==> authority g (<[th := e]> M) ** holder g th e).
    Proof.
      intros Hnone. rewrite /authority /holder fmap_insert.
      iIntros "A". iMod (own_update with "A") as "[$ $]"; last done.
      apply gmap_view_alloc; [by rewrite lookup_fmap Hnone | done | done].
    Qed.

    Lemma holder_delete g M th e :
      authority g M ** holder g th e |-- (|==> authority g (delete th M)).
    Proof.
      rewrite /authority /holder fmap_delete. iIntros "[A F]".
      iMod (own_update_2 with "A F") as "$"; last done.
      apply gmap_view_delete.
    Qed.
  End ghost_laws.

  #[global] Instance not_locked_timeless `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this g th qt : Timeless (not_locked this g th qt).
  Proof. rewrite /not_locked. apply _. Qed.
  #[global] Instance not_locked_exclusive `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this g th : Exclusive1 (not_locked this g th).
  Proof.
    intros q1 q2. rewrite /not_locked. iIntros "[_ A] [_ B]".
    have Hoverlap : ~ ((↑smutex_inv_namespace g : coPset) ## ↑smutex_inv_namespace g).
    { have Hne := nclose_non_empty (smutex_inv_namespace g). set_solver. }
    iDestruct (MutexSets.my_mutexes_exclusive _ _ _ Hoverlap
      with "[$A $B]") as %[].
  Qed.
  #[global] Instance locked_timeless `{Σ : cpp_logic, !G Σ} {σ : genv}
      this g th qt : Timeless (locked this g th qt).
  Proof. rewrite /locked. apply _. Qed.
  #[global] Instance reader_locked_timeless `{Σ : cpp_logic, !G Σ} {σ : genv}
      this g th qt qP : Timeless (reader_locked this g th qt qP).
  Proof. rewrite /reader_locked. apply _. Qed.
  #[global] Instance locked_objective `{Σ : cpp_logic, !G Σ} {σ : genv}
      this g th qt : Objective (locked this g th qt).
  Proof. rewrite /locked /holder /share. apply _. Qed.
  #[global] Instance reader_locked_objective `{Σ : cpp_logic, !G Σ} {σ : genv}
      this g th qt qP : Objective (reader_locked this g th qt qP).
  Proof. rewrite /reader_locked /holder /share. apply _. Qed.
  #[global] Instance locked_exclusive `{Σ : cpp_logic, !G Σ} {σ : genv}
      this g : Exclusive2 (locked this g).
  Proof.
    intros th1 th2 q1 q2. rewrite /locked. iIntros "[_ A] [_ B]".
    iDestruct (full_share_exclusive with "[$A $B]") as %[].
  Qed.
  Lemma reader_writer_exclusive `{Σ : cpp_logic, !G Σ} {σ : genv}
      this g th1 th2 qt1 qt2 qP :
    th1 <> th2 ->
    reader_locked this g th1 qt1 qP -∗ locked this g th2 qt2 -∗ False.
  Proof.
    intros _. rewrite /reader_locked /locked. iIntros "[_ R] [_ W]".
    iApply (full_share_exclusive with "[$W $R]").
  Qed.

  (** sums up the fractions in M and add to initializer [s].
      We need [s] because [Qp] does not have 0. *)
  Definition total (M : reader_map) (s : Qp) : Qp :=
    map_fold (fun _ qr acc => (qr.2 + acc)%Qp) s M.
  Definition reader_entries (M : reader_map) : gmap thread_idT entry :=
    (fun qr => (qr.1, Some qr.2)) <$> M.

  Lemma total_empty s : total ∅ s = s.
  Proof. by rewrite /total map_fold_empty. Qed.
  Lemma total_insert M th qt r s : M !! th = None ->
    total (<[th := (qt,r)]> M) s = (r + total M s)%Qp.
  Proof.
    intros Hnone. rewrite /total map_fold_insert_L; [done | | done].
    intros j1 j2 [qt1 r1] [qt2 r2] acc Hne H1 H2. simpl.
    rewrite !Qp.add_assoc (Qp.add_comm r1 r2). done.
  Qed.
  Lemma total_add M r s : total M (r+s) = (r + total M s)%Qp.
  Proof.
    induction M as [|th [qt qP] M Hnone IH] using map_ind.
    - by rewrite !total_empty.
    - rewrite !total_insert // IH !Qp.add_assoc (Qp.add_comm qP r). done.
  Qed.
  Lemma total_delete M th qt r s : M !! th = Some (qt,r) ->
    total (delete th M) (s+r) = total M s.
  Proof.
    intros Hlookup. rewrite (Qp.add_comm s r) total_add.
    have HM : <[th := (qt,r)]> (delete th M) = M.
    { rewrite insert_delete decide_True // insert_id //. }
    rewrite -{2}HM.
    rewrite total_insert; last apply lookup_delete_eq.
    done.
  Qed.

  Definition max_readers : Z := 2147483647.
  #[global] Arguments max_readers /.
  Definition deposits `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (M : reader_map) : mpred :=
    [∗ map] th ↦ qr ∈ M, not_locked this g th qr.1.

  Definition state `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (P : Qp -> mpred) (n : Z) : mpred :=
    (* thread [th] is the writer *)  
    (∃ th qt, [| n = -1 |] ** authority g {[th := (qt,None)]} **
      not_locked this g th qt) ∨
    (* 0 or more readers; [share g s ** P s] remains in the invariant *)
    (∃ (M : reader_map) (s : Qp),
      [| n = Z.of_nat (size M) /\ n <= max_readers /\ total M s = 1%Qp |] **
      authority g (reader_entries M) ** share g s ** P s ** deposits this g M).

  #[global] Instance state_WeaklyObjective
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g P n
      `{!forall q, Objective (P q)} : WeaklyObjective (state this g P n).
  Proof.
    rewrite /state /authority /share /deposits /not_locked /token. apply _.
  Qed.

  Section state_laws.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.

    Lemma state_bounds this g P n :
      state this g P n |-- [| -1 <= n <= max_readers |].
    Proof.
      rewrite /state. iIntros "[W|R]".
      - iDestruct "W" as (th qt) "(% & _)". iPureIntro. unfold max_readers. lia.
      - iDestruct "R" as (M s) "(% & _)". iPureIntro. lia.
    Qed.

    Lemma deposits_fresh this g M th qt :
      deposits this g M ** not_locked this g th qt |-- [| M !! th = None |].
    Proof.
      rewrite /deposits. iIntros "[D NL]".
      destruct (M !! th) as [qr|] eqn:Hl; last done.
      iDestruct (big_sepM_lookup _ _ _ _ Hl with "D") as "Dup".
      iDestruct (observe_2 False with "NL Dup") as %[].
    Qed.

    Lemma reader_lookup g M th qt qP :
      authority g (reader_entries M) ** holder g th (qt,Some qP) |--
      [| M !! th = Some (qt,qP) |].
    Proof.
      iIntros "H". iDestruct (holder_lookup with "H") as %Hl.
      rewrite /reader_entries lookup_fmap in Hl.
      destruct (M !! th) as [[qt' r]|] eqn:He; rewrite He /= in Hl; simplify_eq; done.
    Qed.

    Lemma writer_lookup g th0 qt0 th qt :
      authority g {[th0 := (qt0,None)]} ** holder g th (qt,None) |--
      [| th0 = th /\ qt0 = qt |].
    Proof.
      iIntros "H". iDestruct (holder_lookup with "H") as %Hl.
      apply lookup_singleton_Some in Hl. iPureIntro. naive_solver.
    Qed.

    Lemma writer_no_reader g th0 qt0 th qt qP :
      authority g {[th0 := (qt0,None)]} ** holder g th (qt,Some qP) |-- False.
    Proof.
      iIntros "H". iDestruct (holder_lookup with "H") as %Hl.
      apply lookup_singleton_Some in Hl. naive_solver.
    Qed.

    Lemma state_lock this g P qt th :
      state this g P 0 ** not_locked this g th qt |--
      (|==> state this g P (-1) ** P 1%Qp ** locked this g th qt).
    Proof.
      rewrite /state /locked. iIntros "[[W|R] NL]".
      - iDestruct "W" as (th0 qt0) "(% & _)". lia.
      - iDestruct "R" as (M s) "(%H & A & S & P & D)".
        have Hsize : size M = 0%nat by lia.
        have Hempty : M = ∅ by apply map_size_empty_iff.
        subst M. rewrite total_empty in H. destruct H as (_ & _ & ->).
        iEval (rewrite /reader_entries fmap_empty) in "A".
        iMod (holder_insert g ∅ th (qt,None) ltac:(done) with "A") as "[A F]".
        iEval (rewrite insert_empty) in "A". iModIntro. iFrame "P F S".
        iLeft. iExists th, qt. iFrame. done.
    Qed.

    Lemma state_unlock this g P n qt th :
      state this g P n ** locked this g th qt ** P 1%Qp |--
      (|==> [| n = -1 |] ** state this g P 0 ** not_locked this g th qt).
    Proof.
      rewrite /state /locked. iIntros "([W|R] & [F S] & P)".
      - iDestruct "W" as (th0 qt0) "(%Hn & A & NL)".
        iDestruct (writer_lookup with "[$A $F]") as %[-> ->].
        iMod (holder_delete with "[$A $F]") as "A".
        iEval (rewrite delete_singleton decide_True //) in "A". iModIntro. iFrame "NL". iSplit; first done.
        iRight. iExists ∅, 1%Qp.
        rewrite /reader_entries fmap_empty /deposits big_sepM_empty.
        iFrame. iPureIntro. rewrite map_size_empty total_empty. unfold max_readers. repeat split; try done; lia.
      - iDestruct "R" as (M s) "(_ & _ & S0 & _)".
        iDestruct (full_share_exclusive with "[$S $S0]") as %[].
    Qed.

    Lemma state_lock_shared this g P n qt th :
      Fractional P -> 0 <= n < max_readers ->
      state this g P n ** not_locked this g th qt |--
      (|==> state this g P (n+1) ** ∃ qP, P qP ** reader_locked this g th qt qP).
    Proof.
      intros HP Hn. rewrite /state /reader_locked.
      iIntros "[[W|R] NL]".
      - iDestruct "W" as (th0 qt0) "(% & _)". lia.
      - iDestruct "R" as (M s) "(%H & A & S & P & D)".
        iDestruct (deposits_fresh with "[$D $NL]") as %Hfresh.
        iMod (holder_insert g (reader_entries M) th (qt,Some (s/2)%Qp)
          with "A") as "[A F]".
        { by rewrite /reader_entries lookup_fmap Hfresh. }
        iDestruct "S" as "[S1 S2]".
        have Hsplit := @fractional _ _ P HP (s/2)%Qp (s/2)%Qp.
        rewrite Qp.div_2 in Hsplit.
        iEval (rewrite Hsplit) in "P".
        iDestruct "P" as "[P1 P2]".
        iModIntro. iSplitR "P2 F S2"; last (iExists (s/2)%Qp; iFrame).
        iRight. iExists (<[th := (qt,(s/2)%Qp)]> M), (s/2)%Qp.
        rewrite /reader_entries fmap_insert /deposits big_sepM_insert //.
        iFrame. iPureIntro. rewrite map_size_insert_None //.
        destruct H as (Hcount & Hbound & Htotal).
        split; first by rewrite Nat2Z.inj_succ -Hcount; lia.
        split; first lia.
        rewrite total_insert // -total_add Qp.div_2. exact Htotal.
    Qed.

    Lemma state_unlock_shared this g P n qt th qP :
      Fractional P ->
      state this g P n ** reader_locked this g th qt qP ** P qP |--
      (|==> [| 0 < n <= max_readers |] **
        state this g P (n-1) ** not_locked this g th qt).
    Proof.
      intros HP. rewrite /state /reader_locked.
      iIntros "([W|R] & [F S] & P)".
      - iDestruct "W" as (th0 qt0) "(_ & A & _)".
        iDestruct (writer_no_reader with "[$A $F]") as %[].
      - iDestruct "R" as (M s) "(%H & A & S0 & P0 & D)".
        iDestruct (reader_lookup with "[$A $F]") as %Hl.
        iMod (holder_delete with "[$A $F]") as "A".
        iEval (rewrite /deposits (big_sepM_delete _ _ _ _ Hl)) in "D".
        iDestruct "D" as "[NL D]".
        have Hsize : (0 < size M)%nat.
        { destruct (decide (M = ∅)) as [->|Hne]; first by rewrite lookup_empty in Hl.
          have Hsz : size M <> 0%nat by intro Hz; apply map_size_empty_iff in Hz.
          lia. }
        iModIntro. iFrame "NL". iSplit; first (iPureIntro; lia).
        iRight. iExists (delete th M), (s+qP)%Qp.
        rewrite /reader_entries fmap_delete /deposits.
        rewrite !fractional. iFrame.
        iPureIntro. rewrite map_size_delete_Some; last by eauto.
        destruct H as (Hcount & Hbound & Htotal).
        split.
        + rewrite Nat2Z.inj_pred.
          * by rewrite -Z.sub_1_r Hcount.
          * exact Hsize.
        + split; first lia.
          rewrite (total_delete M th qt qP s Hl). exact Htotal.
    Qed.

    Lemma deposits_full_token_empty this g M :
      token g 1$m ** deposits this g M |-- [| M = ∅ |].
    Proof.
      induction M as [|th [qt qP] M Hnone IH] using map_ind; first by iIntros "_".
      rewrite /deposits big_sepM_insert // /not_locked /=.
      iIntros "[T [[T0 _] _]]".
      iDestruct (full_token_exclusive with "[$T $T0]") as %[].
    Qed.

    Lemma state_destroy this g P n :
      state this g P n ** token g 1$m |-- [| n = 0 |] ** P 1%Qp.
    Proof.
      rewrite /state. iIntros "[[W|R] T]".
      - iDestruct "W" as (th qt) "(_ & _ & NL)".
        iEval (rewrite /not_locked) in "NL". iDestruct "NL" as "[T0 _]".
        iDestruct (full_token_exclusive with "[$T $T0]") as %[].
      - iDestruct "R" as (M s) "(%H & _ & _ & P & D)".
        iDestruct (deposits_full_token_empty with "[$T $D]") as %->.
        rewrite map_size_empty total_empty in H. destruct H as (-> & _ & ->).
        iFrame. done.
    Qed.
  End state_laws.

  Definition mutex_inv `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (P : Qp -> mpred) : mpred :=
    ∃ n : Z, this ,, _field "MySharedMutex::sharers" |-> atomic.R "int" 1$m n **
      state this g P n.

  Definition R `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {HAS_THREADS : HasStdThreads Σ} {σ : genv}
      (g : gname) (q : cQp.t) (P : Qp -> mpred) : Rep :=
    structR class_name q$m ** as_Rep (fun this =>
      [| Fractional P /\ (forall qP, Objective (P qP)) |] **
      cinv (smutex_inv_namespace g) g.(cinv_gname) (mutex_inv this g P) **
      cinv_own g.(cinv_gname) q).
  #[global] Hint Opaque token not_locked locked reader_locked R :
    sl_opacity typeclass_instances.
  #[only(cfractional,ascfractional,cfracvalid)] derive R.
  #[global] Instance R_type_ptr `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      {HAS_THREADS : HasStdThreads Σ} g q P :
      Observe (type_ptrR cpp_ty) (R g q P).
  Proof. rewrite /R /cpp_ty. apply _. Qed.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
      WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.
  #[global] Instance mutex_inv_WeaklyObjective
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g P
      `{!forall qP, Objective (P qP)} : WeaklyObjective (mutex_inv this g P).
  Proof. rewrite /mutex_inv. apply _. Qed.

  Definition globals `{Σ : cpp_logic} {σ : genv} (q : cQp.t) : mpred :=
    _global "std::memory_order_seq_cst" |->
      primR "enum std::memory_order" q
        (memory_order.to_val memory_order.seq_cst).
  #[global] Arguments globals /.

End CustomSharedMutexPreds.

Module custom_shared_mutex.
  Import CustomSharedMutexPreds.
  #[local] Existing Instances holders_own holders_upd holders_valid.
  Module Spec := shared_mutex_spec CustomSharedMutexPreds.
  Abbreviation IR := CustomSharedMutexPreds.R.
  Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!CustomSharedMutexPreds.G Σ}.
    Context `{MOD : source ⊧ σ}.

    cpp.spec "MySharedMutex::MySharedMutex()" as ctor_spec with
      (\exact Reduce Spec.ctor_spec).
    cpp.spec "MySharedMutex::~MySharedMutex()" as dtor_spec with
      (\exact Reduce Spec.dtor_spec).
    cpp.spec "MySharedMutex::lock()" as lock_spec_alt with
      (\this this \prepost{qg} globals qg
       \exact Reduce (Spec.lock_spec_alt this)).
    cpp.spec "MySharedMutex::unlock()" as unlock_spec_alt with
      (\this this \prepost{qg} globals qg
       \exact Reduce (Spec.unlock_spec_alt this)).
    cpp.spec "MySharedMutex::lock()" as lock_spec with
      (\this this \prepost{qg} globals qg
       \exact Reduce (Spec.lock_spec this)).
    cpp.spec "MySharedMutex::unlock()" as unlock_spec with
      (\this this \prepost{qg} globals qg
       \exact Reduce (Spec.unlock_spec this)).
    cpp.spec "MySharedMutex::lock_shared()" as lock_shared_spec with
      (\this this \prepost{qg} globals qg
       \exact Reduce (Spec.lock_shared_spec this)).
    cpp.spec "MySharedMutex::unlock_shared()" as unlock_shared_spec with
      (\this this \prepost{qg} globals qg
       \exact Reduce (Spec.unlock_shared_spec this)).

    Lemma lock_spec_equiv_lock_spec_alt : lock_spec ⊣⊢ lock_spec_alt.
    Proof.
      rewrite /lock_spec /lock_spec_alt /specify.
      do 2 f_equiv. intros this xs K. rewrite !add_with_equiv.
      f_equiv=> qg. by rewrite !add_prepost_equiv Spec.lock_spec_equiv_lock_spec_alt.
    Qed.
    Lemma unlock_spec_equiv_unlock_spec_alt : unlock_spec ⊣⊢ unlock_spec_alt.
    Proof.
      rewrite /unlock_spec /unlock_spec_alt /specify.
      do 2 f_equiv. intros this xs K. rewrite !add_with_equiv.
      f_equiv=> qg. by rewrite !add_prepost_equiv Spec.unlock_spec_equiv_unlock_spec_alt.
    Qed.

    Definition bi_later_exist_F := [FWD] @bi.later_exist.
    Definition bi_later_sep_F := [FWD] @bi.later_sep.
    #[local] Hint Resolve bi_later_exist_F bi_later_sep_F : br_hints.

    #[program]
    Definition do_load_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{g q P} p |-> IR g q P
      \proving{K (_ : IsExistential K)}
        std.atomic.do_load "int" (BASE (p ,, o_field σ "MySharedMutex::sharers")) K
      \instantiate K := (fun n : Z => p |-> IR g q P **
        [| -1 <= n <= max_readers |])
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M IR]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & %HP & #CI & CO)".
      rewrite /std.atomic.do_load.
      iAcIntro. rewrite /commit_acc.
      iInv (smutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (n) "(>L & State)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [|iModIntro]; first set_solver.
      iExists n, (1$m)%cQp.
      iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      iDestruct (state_bounds with "State") as %Hbounds.
      iMod ("Hclose" with "[L State]") as "_".
      { iNext. rewrite /mutex_inv. iExists n.
        iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /IR _at_sep _at_as_Rep.
      iFrame "CI S CO". auto.
    Qed.
    #[local] Hint Resolve do_load_C : sl_opacity.

    #[program]
    Definition do_writer_cas_C (p expected_p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{g q P} p |-> IR g q P
      \consuming{th qt} not_locked p g th qt
      \proving{K (_ : IsExistential K)}
        std.atomic.do_compare_exchange "int" false
          (BASE (p ,, o_field σ "MySharedMutex::sharers")) expected_p 0%Z (-1)%Z K
      \instantiate K := (fun b : bool =>
        (∃ actual : Z, expected_p |-> intR 1$m actual) ** p |-> IR g q P **
        if b then P 1%Qp ** locked p g th qt else not_locked p g th qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M [IR NL]]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & %HP & #CI & CO)".
      rewrite /std.atomic.do_compare_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv (smutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (n) "(>L & State)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [|iModIntro]; first set_solver.
      iExists n. iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L State]") as "_".
        { iNext. rewrite /mutex_inv. iExists n.
          iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros (b n') "[%Hres L]". iMod "Y" as "_".
        destruct Hres as [(-> & -> & ->)|(-> & Hne & ->)].
        + iMod (state_lock with "[$State $NL]") as "(State & P & Locked)".
          iMod ("Hclose" with "[L State]") as "_".
          { iNext. rewrite /mutex_inv. iExists (-1)%Z.
            iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
          iModIntro. iIntros "Expected".
          rewrite /IR _at_sep _at_as_Rep. iFrame "CI S CO P Locked".
          iSplitL "Expected"; first (iExists 0%Z; iFrame). done.
        + iMod ("Hclose" with "[L State]") as "_".
          { iNext. rewrite /mutex_inv. iExists n.
            iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
          iModIntro. iIntros "Expected".
          rewrite /IR _at_sep _at_as_Rep. iFrame "CI S CO NL".
          iSplitL "Expected"; first (iExists n; iFrame). done.
    Qed.
    #[local] Hint Resolve do_writer_cas_C : sl_opacity.

    #[program]
    Definition do_reader_cas_C (p expected_p : ptr) (expected : Z) :=
      \cancelx
      \using denoteModule source
      \consuming{g q P} p |-> IR g q P
      \consuming{th qt} not_locked p g th qt
      \guard (0 <= expected < max_readers)
      \proving{K (_ : IsExistential K)}
        std.atomic.do_compare_exchange "int" false
          (BASE (p ,, o_field σ "MySharedMutex::sharers"))
          expected_p expected (expected+1)%Z K
      \instantiate K := (fun b : bool =>
        (∃ actual : Z, expected_p |-> intR 1$m actual) ** p |-> IR g q P **
        if b then (∃ qP, P qP ** reader_locked p g th qt qP)%I
        else not_locked p g th qt)
      \end@{mpredI}.
    Next Obligation.
      intros. have Hrange : 0 <= expected < max_readers by assumption.
      iIntros "[#M [IR NL]]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & %HP & #CI & CO)".
      rewrite /std.atomic.do_compare_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv (smutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (n) "(>L & State)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [|iModIntro]; first set_solver.
      iExists n. iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L State]") as "_".
        { iNext. rewrite /mutex_inv. iExists n.
          iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros (b n') "[%Hres L]". iMod "Y" as "_".
        destruct Hres as [(-> & -> & ->)|(-> & Hne & ->)].
        + iMod (state_lock_shared _ _ _ _ _ _ (proj1 HP) Hrange
            with "[$State $NL]") as "[State Result]".
          iMod ("Hclose" with "[L State]") as "_".
          { iNext. rewrite /mutex_inv. iExists (expected+1)%Z.
            iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
          iModIntro. iIntros "Expected".
          rewrite /IR _at_sep _at_as_Rep. iFrame "CI S CO Result".
          iSplitL "Expected"; first (iExists expected; iFrame). done.
        + iMod ("Hclose" with "[L State]") as "_".
          { iNext. rewrite /mutex_inv. iExists n.
            iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
          iModIntro. iIntros "Expected".
          rewrite /IR _at_sep _at_as_Rep. iFrame "CI S CO NL".
          iSplitL "Expected"; first (iExists n; iFrame). done.
    Qed.
    #[local] Hint Resolve do_reader_cas_C : sl_opacity.

    #[program]
    Definition do_store_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{g q P} p |-> IR g q P
      \consuming{th qt} locked p g th qt
      \consuming P 1%Qp
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store "int" (BASE (p ,, o_field σ "MySharedMutex::sharers")) 0%Z K
      \instantiate K := (p |-> IR g q P ** not_locked p g th qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M (IR & Locked & P)]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & %HP & #CI & CO)".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc.
      iInv (smutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (n) "(>L & State)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [|iModIntro]; first set_solver.
      iExists n. iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      iMod (state_unlock with "[$State $Locked $P]") as "(_ & State & NL)".
      iMod ("Hclose" with "[L State]") as "_".
      { iNext. rewrite /mutex_inv. iExists 0%Z.
        iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /IR _at_sep _at_as_Rep. iFrame "CI S CO NL". done.
    Qed.
    #[local] Hint Resolve do_store_C : sl_opacity.

    #[program]
    Definition do_decrement_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{g q P} p |-> IR g q P
      \consuming{th qt qP} reader_locked p g th qt qP
      \consuming P qP
      \proving{K (_ : IsExistential K)}
        (* FIXME std.atomic.do_op is supposed to be local to the atomic module.
         Is it fine to use it here directly? *)
        std.atomic.do_op "int" (atomic_eval int_rank.Iint Signed Z.add (-1))
          (BASE (p ,, o_field σ "MySharedMutex::sharers")) K
      \instantiate K := (fun _ : Z => p |-> IR g q P ** not_locked p g th qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M (IR & Locked & P)]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & %HP & #CI & CO)".
      rewrite /std.atomic.do_op.
      iAcIntro. rewrite /commit_acc.
      iInv (smutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (n) "(>L & State)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [|iModIntro]; first set_solver.
      iExists n. iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      iMod (state_unlock_shared _ _ _ _ _ _ _ (proj1 HP)
        with "[$State $Locked $P]") as "(%Hbounds & State & NL)".
      have Hop : atomic_eval int_rank.Iint Signed Z.add (-1) n = (n-1)%Z.
      { unfold atomic_eval. rewrite to_signed_id; unfold max_readers in *; simpl in *; lia. }
      iEval (rewrite Hop) in "L".
      iMod ("Hclose" with "[L State]") as "_".
      { iNext. rewrite /mutex_inv. iExists (n-1)%Z.
        iSplitL "L"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /IR _at_sep _at_as_Rep. iFrame "CI S CO NL". done.
    Qed.
    #[local] Hint Resolve do_decrement_C : sl_opacity.

    Lemma mysharedmutex_lock_alt_proof : verify[source] lock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wp_while (fun _ => emp); go.
      ework with br_erefl.
      go. wp_if; go.
    Qed.

    Lemma mysharedmutex_unlock_alt_proof : verify[source] unlock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec; go.
    Qed.

    Lemma mysharedmutex_lock_shared_proof : verify[source] lock_shared_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wname [_ |-> uninitR _ _] "Val".
      iDestruct (_at_mono _ _ (uninitR_anyR "int" 1$m) with "Val") as "?".
      wp_do_while (fun _ => emp); go.
      repeat (first [case_bool_decide | match goal with b : bool |- _ => destruct b end | wp_if]; go).
      all: try (ework with br_erefl; go).
      all: repeat (first [case_bool_decide | match goal with b : bool |- _ => destruct b end | wp_if]; go).
      all: try match goal with
        | Hb : -1 <= ?v |- _ =>
          have Hrange : 0 <= v < max_readers by unfold max_readers; lia
        end.
      all: try (ework with br_erefl; go).
      all: repeat (first [case_bool_decide | match goal with b : bool |- _ => destruct b end | wp_if]; go).
      all: ework with br_erefl.
      all: go.
      all: repeat (first [case_bool_decide | match goal with b : bool |- _ => destruct b end | wp_if]; go).
      all: exfalso; simpl in *; congruence.
      Unshelve. all: exact 1%Qp.
    Qed.

    Lemma mysharedmutex_unlock_shared_proof : verify[source] unlock_shared_spec.
    Proof using MOD HAS_THREADS.
      verify_spec; go.
    Qed.

    Lemma mysharedmutex_ctor_proof : verify[source] "MySharedMutex::MySharedMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      (* Retain the body while the member constructor initializes the counter;
         its update modality permits allocation of the mutex invariant. *)
      match goal with |- context[wp ?tu ?rho ?s ?K] =>
        rewrite (lock (wp tu rho s K)) end.
      go. rewrite -lock. iApply fupd_wp.
      wname [structR] "S".
      wname [P] "P".
      wname [_ |-> atomic.R _ _ _] "L".
      iMod (own_alloc (1%Qp : fracR)) as (gt) "T"; first done.
      iMod (own_alloc (1%Qp : fracR)) as (gs) "Share"; first done.
      iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : holdersR)) as (gh) "A".
      { apply gmap_view_auth_valid. }
      iMod (cinv_alloc ⊤ N
        (mutex_inv this (MkGname gt gs gh 1%positive N) P)
        with "[L P Share A]") as (gi) "[#CI CO]"; last first.
      - iModIntro. go. iExists (MkGname gt gs gh gi N).
        rewrite /IR /R _at_sep _at_as_Rep /token /smutex_inv_namespace /=.
        iFrame "CI S CO T". auto.
      - iNext. rewrite /mutex_inv /state. iExists 0%Z. iFrame "L".
        iRight. iExists ∅, 1%Qp.
        rewrite /authority /share /reader_entries fmap_empty /deposits big_sepM_empty /=.
        iFrame "P Share A". iPureIntro.
        rewrite map_size_empty total_empty. unfold max_readers. repeat split; try done; lia.
    Qed.

    Lemma mysharedmutex_dtor_proof : verify[source] "MySharedMutex::~MySharedMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite /IR /R /mutex_inv.
      work.
      wname [cinv] "#CI".
      wname [cinv_own] "CO".
      wname [CustomSharedMutexPreds.token] "T".
      iMod (cinv_cancel with "CI CO") as "Inv"; [done..|].
      go.
      iDestruct "Inv" as (n) "[L State]".
      iDestruct (state_destroy with "[$State $T]") as "[%Hn P]".
      subst n. ego $usenamed=true with br_erefl.
    Qed.

    Lemma mysharedmutex_lock_proof : verify[source] lock_spec.
    Proof using MOD HAS_THREADS.
      rewrite lock_spec_equiv_lock_spec_alt. exact mysharedmutex_lock_alt_proof.
    Qed.
    Lemma mysharedmutex_unlock_proof : verify[source] unlock_spec.
    Proof using MOD HAS_THREADS.
      rewrite unlock_spec_equiv_unlock_spec_alt. exact mysharedmutex_unlock_alt_proof.
    Qed.

    Definition standard_library_specs : mpred :=
      std.atomic.ctor "int" ** std.atomic.dtor "int" **
      std.atomic.compare_exchange_strong_1 "int" **
      std.atomic.cast "int" ** std.atomic.assign "int" **
      std.atomic.fetch_unop "int" (op_name := OOMinusMinus).

    Lemma link :
      denoteModule source ** standard_library_specs |--
      ctor_spec ** dtor_spec ** lock_spec ** unlock_spec **
      lock_shared_spec ** unlock_shared_spec.
    Proof using MOD HAS_THREADS.
      rewrite /standard_library_specs.
      work.
      wapply mysharedmutex_ctor_proof.
      wapply mysharedmutex_dtor_proof.
      wapply mysharedmutex_lock_proof.
      wapply mysharedmutex_unlock_proof.
      wapply mysharedmutex_lock_shared_proof.
      wapply mysharedmutex_unlock_shared_proof.
      work.
    Qed.
  End with_Σ.
End custom_shared_mutex.
