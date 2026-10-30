(** Exclusive migration of a payload partition. This changes ghost protocol
    identities, never the C++ handles, allocation, or reference count. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.shared_ptr.handle_liveness.
Require Import skylabs.brick.libstdcpp.shared_ptr.token_pool.
Require Import iris.algebra.excl iris.algebra.frac.

Set Default Goal Selector "!".
Import linearity.

Section redistribution.
  Context `{Sigma : cpp_logic} {CU : genv}.
  #[local] Existing Instance br.ghost.excl_inG.
  #[local] Existing Instance br.ghost.frac_inG.

  #[local] Lemma indexed_ownership {A} (xs : list A) (P : A -> mpred) fallback :
    ([∗ list] x ∈ xs, P x) -|-
    ([∗ list] i ∈ seq 0 (length xs),
      match nth_error xs i with Some x => P x | None => fallback end).
  Proof.
    induction xs as [| x xs IH]; first reflexivity.
    cbn [length seq]. rewrite !big_sepL_cons.
    rewrite <- fmap_S_seq, big_sepL_fmap.
    cbn [nth_error]. rewrite <- IH. reflexivity.
  Qed.

  #[local] Lemma conditional_sep_lists (out : nat -> bool)
      (P Q : nat -> mpred) indices :
    ([∗ list] i ∈ indices, P i) ** ([∗ list] i ∈ indices, Q i) -|-
    ([∗ list] i ∈ indices,
      (if out i then Q i else P i) ** (if out i then P i else Q i)).
  Proof.
    rewrite <- big_sepL_sep. apply big_sepL_proper.
    intros k i Hi. destruct (out i); first apply bi.sep_comm. reflexivity.
  Qed.

  #[local] Lemma alloc_rights n :
    (emp : mpred) |-- (|==> Exists names : list gname,
      [| length names = n |] **
      ([∗ list] name ∈ names, own (A := exclR unitO) name (Excl ())))%I.
  Proof.
    induction n as [| n IH].
    { rewrite <- bupd_intro. go. iExists []. go. }
    rewrite <- bi.emp_sep at 1.
    etrans; first (apply bi.sep_mono;
      [exact IH | exact (own_alloc (PROP := mpredI) (A := exclR unitO) (Excl ()) ltac:(done))]).
    rewrite bupd_sep. apply bupd_mono. go.
    match goal with names : list gname |- _ => iExists (t :: names) end. go.
  Qed.

  #[local] Lemma alloc_handles n :
    (emp : mpred) |-- (|==> Exists names : list gname,
      [| length names = n |] **
      ([∗ list] name ∈ names, own (A := fracR) name 1%Qp))%I.
  Proof.
    induction n as [| n IH].
    { rewrite <- bupd_intro. go. iExists []. go. }
    rewrite <- bi.emp_sep at 1.
    etrans; first (apply bi.sep_mono;
      [exact IH | exact (own_alloc (PROP := mpredI) (A := fracR) 1%Qp ltac:(done))]).
    rewrite bupd_sep. apply bupd_mono. go.
    match goal with names : list gname |- _ => iExists (t :: names) end. go.
  Qed.
  Definition protocol_tokens id (out : nat -> bool) : mpred :=
    [∗ list] i ∈ allPieceIds,
      if out i then pieceHandle id 1 i else pieceRight id i.

  Definition invariant_tokens id (out : nat -> bool) : mpred :=
    [∗ list] i ∈ allPieceIds,
      if out i then pieceRight id i else pieceHandle id 1 i.

  Definition payload_pieces (R : nat -> Rep) (p : ptr) (out : nat -> bool) : mpred :=
    [∗ list] i ∈ allPieceIds, if out i then p |-> R i else emp.

  Definition handle_cells ty id (p : ptr) (handles : nat -> ptr)
      (out : nat -> bool) : mpred :=
    [∗ list] i ∈ allPieceIds,
      if out i then handles i |-> SharedPtrHandleR ty 1$m p (dataLoc id) else emp.

  #[local] Hint Opaque protocol_tokens invariant_tokens payload_pieces
    handle_cells pieceHandle pieceRight sptrInv payload_destructible
    payload_releasable payload_allocation
    SharedPtrHandleR : sl_opacity.

  #[local] Lemma alloc_protocol control managed cleanup (out : nat -> bool) :
    (emp : mpred) |-- (|==> Exists id : CtrlBlockId,
      [| dataLoc id = control /\ payload_type id = managed /\
         lengthN (pieceRightLocs id) = N.pos maxContention /\
         lengthN (pieceHandleLocs id) = N.pos maxContention /\
         payload_delete id = cleanup |] **
      protocol_tokens id out ** invariant_tokens id out)%I.
  Proof.
    rewrite <- bi.emp_sep at 1.
    etrans; first (apply bi.sep_mono;
      [exact (alloc_rights (Pos.to_nat maxContention)) |
       exact (alloc_handles (Pos.to_nat maxContention))]).
    rewrite bupd_sep. apply bupd_mono. go.
    match goal with rights : list gname, handles : list gname |- _ =>
      iExists {| pieceRightLocs := rights; pieceHandleLocs := handles;
        dataLoc := control; payload_type := managed; payload_delete := cleanup |}
    end.
    unfold protocol_tokens, invariant_tokens, pieceRight, pieceHandle.
    cbn [pieceRightLocs pieceHandleLocs dataLoc payload_type payload_delete].
    rewrite <- big_sepL_sep.
    setoid_rewrite (indexed_ownership _ (fun name => own (A := exclR unitO) name (Excl ())) emp).
    setoid_rewrite (indexed_ownership _ (fun name => own (A := fracR) name 1%Qp) False%I).
    unfold lengthN, allPieceIds.
    rewrite <- conditional_sep_lists.
    repeat match goal with
    | Hlen : length ?xs = _ |- context[length ?xs] => rewrite Hlen
    end.
    go.
  Qed.

  #[local] Lemma token_pair_agrees id i (out inside : bool) :
    (i < length (pieceRightLocs id))%nat ->
    (if out then pieceHandle id 1 i else pieceRight id i) **
    (if inside then pieceRight id i else pieceHandle id 1 i)
    |-- [| inside = out |] ** pieceHandle id 1 i.
  Proof.
    intros Hi.
    (* Retired copy rights contain only ghost ownership, not object storage. *)
    assert (HA : Affine (pieceRight id i)).
    { apply monPred_bi_affine, uPred_affine. }
    destruct out, inside.
    { etrans; first (apply bi.sep_elim_l; typeclasses eauto). go. }
    { rewrite pieceHandle_full_conflict. go. }
    { rewrite (TokenPool.pieceRight_exclusive id i Hi). go. }
    { etrans; first (apply bi.sep_elim_r; typeclasses eauto). go. }
  Qed.

  #[local] Lemma tokens_agree id out inside :
    lengthN (pieceRightLocs id) = N.pos maxContention ->
    protocol_tokens id out ** invariant_tokens id inside |--
      [| forall i, i ∈ allPieceIds -> inside i = out i |] **
      invariant_tokens id (fun _ => false).
  Proof.
    intros Hlength. unfold protocol_tokens, invariant_tokens.
    rewrite <- big_sepL_sep.
    etrans.
    { apply big_op.big_sepL_mono_elem. intros i Hi. apply token_pair_agrees.
      unfold allPieceIds in Hi. apply elem_of_seq in Hi.
      unfold lengthN in Hlength. lia. }
    rewrite big_sepL_sep lemmas.big_sepL_only_provable Forall_forall. go.
  Qed.

  #[local] Lemma payload_pieces_partition R p out :
    payload_pieces R p out ** payload_pieces R p (fun i => negb (out i))
      -|- p |-> ([∗ list] i ∈ allPieceIds, R i).
  Proof.
    unfold payload_pieces. rewrite <- big_sepL_sep. rewrite _at_big_sepL.
    apply big_sepL_proper. intros k i Hi.
    destruct (out i); simpl; rewrite ?bi.sep_emp ?bi.emp_sep; reflexivity.
  Qed.
  (** Handle addresses are arguments, not hidden existential witnesses. *)
  Definition allPiecesAndObjs ty R id (p : ptr) (handles : nat -> ptr)
      (out : nat -> bool) : mpred :=
    [∗ list] i ∈ allPieceIds,
      if out i then p |-> R i ** handles i |-> SharedPtrR ty 1$m id i R p
      else pieceRight id i.

  Definition protocol_knowledge ty id R (p : ptr) : mpred :=
    [| delete_compat ty (payload_type id) /\ p <> nullptr /\
       lengthN (pieceRightLocs id) = N.pos maxContention /\
       lengthN (pieceHandleLocs id) = N.pos maxContention |] **
    payload_releasable id R **
    inv nroot (Exists out, sptrInv id R p out).

  #[local] Instance protocol_knowledge_persistent ty id R p :
    Persistent (protocol_knowledge ty id R p) := _.
  #[local] Hint Opaque allPiecesAndObjs protocol_knowledge : sl_opacity.
  #[local] Opaque payload_releasable payload_allocation.

  #[local] Lemma census_knowledge ty R id p handles out live :
    live ∈ allPieceIds -> out live = true ->
    allPiecesAndObjs ty R id p handles out |--
      protocol_knowledge ty id R p ** allPiecesAndObjs ty R id p handles out.
  Proof.
    intros Hi Hlive. unfold allPiecesAndObjs.
    rewrite (big_op.big_sepL_difference_singleton live) //.
    2: { unfold allPieceIds. apply NoDup_seq. }
    rewrite Hlive. unfold SharedPtrR, protocol_knowledge. go.
  Qed.

  #[local] Lemma census_split ty R id p handles out :
    allPiecesAndObjs ty R id p handles out |--
      handle_cells ty id p handles out ** protocol_tokens id out ** payload_pieces R p out.
  Proof.
    unfold allPiecesAndObjs, handle_cells, protocol_tokens, payload_pieces.
    rewrite <- !big_sepL_sep.
    apply big_sepL_mono. intros k i Hi.
    destruct (out i); last go. unfold SharedPtrR. go.
  Qed.

  #[local] Lemma census_close ty R id p handles out :
    protocol_knowledge ty id R p ** handle_cells ty id p handles out **
    protocol_tokens id out ** payload_pieces R p out |--
      allPiecesAndObjs ty R id p handles out.
  Proof.
    unfold allPiecesAndObjs, handle_cells, protocol_tokens, payload_pieces.
    rewrite -!bi.sep_assoc -!big_sepL_sep.
    rewrite -(bi.wand_elim_l' _ _ _ (bi.wand_entails _ _
      (big_sepL_impl (fun _ i =>
        (if out i then handles i |-> SharedPtrHandleR ty 1$m p (dataLoc id) else emp) **
        (if out i then pieceHandle id 1 i else pieceRight id i) **
        (if out i then p |-> R i else emp))%I
        (fun _ i => if out i then p |-> R i **
          handles i |-> SharedPtrR ty 1$m id i R p else pieceRight id i)%I
        allPieceIds))).
    setoid_rewrite bi.pure_impl_forall.
    unfold protocol_knowledge. go.
    match goal with Hfound : allPieceIds !! _ = Some ?i |- _ =>
      rename i into index; rename Hfound into Hlookup
    end.
    assert (Hbound : (N.of_nat index < N.pos maxContention)%N).
    { apply list_elem_of_lookup_2 in Hlookup.
      unfold allPieceIds in Hlookup. apply elem_of_seq in Hlookup. lia. }
    destruct (out index).
    { unfold SharedPtrR. go. }
    { go. }
  Qed.
  Definition counter_allocation id p count : mpred :=
    dataLoc id ., (SP_counted_base .:: Nid "_M_use_count") |-> intR 1$m (Z.of_N count) **
    payload_allocation id p.
  #[local] Hint Opaque counter_allocation : sl_opacity.
  #[local] Transparent payload_releasable payload_allocation.

  #[local] Lemma countLN_agree (left right : nat -> bool) :
    (forall i, i ∈ allPieceIds -> left i = right i) ->
    countLN left allPieceIds = countLN right allPieceIds.
  Proof.
    unfold countLN. generalize allPieceIds as indices.
    intros indices. induction indices as [| i indices IH]; intros Hsame; first reflexivity.
    assert (Hhead : left i = right i) by (apply Hsame; by left).
    assert (Htail : forall j, j ∈ indices -> left j = right j)
      by (intros j Hj; apply Hsame; by right).
    rewrite !filter_cons Hhead.
    destruct (decide (right i)); simpl; rewrite ?lengthN_cons (IH Htail); reflexivity.
  Qed.

  #[local] Lemma reclaim_protocol id R p out inside :
    lengthN (pieceRightLocs id) = N.pos maxContention ->
    (0 < countLN out allPieceIds)%N ->
    protocol_tokens id out ** sptrInv id R p inside |--
      invariant_tokens id (fun _ => false) **
      counter_allocation id p (countLN out allPieceIds) **
      payload_pieces R p (fun i => negb (out i)).
  Proof.
    intros Hlength Hlive. unfold sptrInv. fold (invariant_tokens id inside).
    wapply (tokens_agree id out inside Hlength). go.
    match goal with H : forall i, i ∈ allPieceIds -> inside i = out i |- _ =>
      pose proof (countLN_agree inside out H) as Hcount;
      assert (Hpieces :
        ([∗ list] i ∈ allPieceIds, if inside i then emp else p |-> R i) -|-
        payload_pieces R p (fun i => negb (out i)))
        by (unfold payload_pieces; apply big_sepL_proper; intros k i Hi;
            apply list_elem_of_lookup_2 in Hi; rewrite (H i Hi);
            destruct (out i); reflexivity)
    end.
    rewrite Hcount bool_decide_false; last lia.
    rewrite Hpieces. unfold counter_allocation. go.
  Qed.

  #[local] Lemma retired_protocol id R p :
    invariant_tokens id (fun _ => false) |-- Exists out, sptrInv id R p out.
  Proof.
    go. iExists (fun _ => false).
    rewrite sptrInv_retired.
    { unfold invariant_tokens. go. }
    { unfold countLN. generalize allPieceIds as indices.
      intros indices. induction indices as [| i indices IH]; first reflexivity.
      rewrite filter_cons. simpl. exact IH. }
  Qed.

  #[local] Lemma active_protocol id R p out :
    (0 < countLN out allPieceIds)%N ->
    invariant_tokens id out ** counter_allocation id p (countLN out allPieceIds) **
    payload_pieces R p (fun i => negb (out i)) |-- Exists actual, sptrInv id R p actual.
  Proof.
    intros Hlive. go. iExists out.
    unfold sptrInv. rewrite bool_decide_false; last lia.
    unfold invariant_tokens, counter_allocation, payload_pieces.
    assert (Hpiece : forall i,
      (if negb (out i) then p |-> R i else emp) -|-
      (if out i then emp else p |-> R i)).
    { intros i. destruct (out i); reflexivity. }
    setoid_rewrite Hpiece. go.
  Qed.

  (** Repartitioning requires every live handle and every unused acquisition
      right. The whole payload, not each individual piece, must be equivalent.
      Old persistent invariant assertions are not rewritten: the old protocol
      is retired and the result uses newly allocated ghost names.

      Timelessness permits opening the old invariant without executing C++.
      Weak objectivity permits allocating the new invariant. The regression
      instantiates an equality-ordered SC index, where weak objectivity holds
      for every assertion. For other thread-view orders, the allocation-token
      interface does not currently discharge this premise automatically. *)
  Lemma redistributePayloadOwnership ty (Rold Rnew : nat -> Rep)
      id p handles out live
      (Htimeless : Timeless (Exists actual, sptrInv id Rold p actual))
      (Hobjective : forall fresh,
        WeaklyObjective (Exists actual, sptrInv fresh Rnew p actual)) :
    live ∈ allPieceIds -> out live = true ->
    (forall payload : ptr,
      payload |-> ([∗ list] i ∈ allPieceIds, Rold i) -|-
      payload |-> ([∗ list] i ∈ allPieceIds, Rnew i)) ->
    allPiecesAndObjs ty Rold id p handles out |--
      |={⊤}=> Exists fresh : CtrlBlockId,
        [| dataLoc fresh = dataLoc id /\ payload_type fresh = payload_type id |] **
        allPiecesAndObjs ty Rnew fresh p handles out.
  Proof.
    intros Hi Hout Hwhole.
    assert (Hlive : (0 < countLN out allPieceIds)%N).
    { eapply countLN_positive_of_member; eauto. }
    assert (Hdestruct : payload_releasable id Rold |--
      payload_releasable id Rnew).
    { unfold payload_releasable.
      destruct (payload_delete id) as [[op alignment]|];
        unfold payload_deletable, payload_destructible;
        setoid_rewrite <- Hwhole; reflexivity. }
    assert (Hrepartition : payload_pieces Rold p out **
      payload_pieces Rold p (fun i => negb (out i)) |--
      payload_pieces Rnew p out ** payload_pieces Rnew p (fun i => negb (out i))).
    { rewrite !payload_pieces_partition Hwhole. reflexivity. }
    wapply (census_knowledge ty Rold id p handles out live Hi Hout). go.
    wapply (census_split ty Rold id p handles out). go.
    unfold protocol_knowledge. go.
    wapply (inv_acc_timeless ⊤ nroot
      (Exists actual, sptrInv id Rold p actual) ltac:(set_solver)). go.
    match goal with actual : nat -> bool |- _ =>
      wapply (reclaim_protocol id Rold p out actual ltac:(assumption) Hlive)
    end.
    go.
    wapply (retired_protocol id Rold p). go.
    wapply (bi.wand_elim_l (Exists actual, sptrInv id Rold p actual)
      (|={⊤ ∖ ↑nroot,⊤}=> emp)%I). go.
    iExists t. go.
    wapply Hrepartition. go.
    wapply (alloc_protocol (dataLoc id) (payload_type id) (payload_delete id) out). go.
    rename t into freshid.
    assert (Hcells : handle_cells ty id p handles out -|-
      handle_cells ty freshid p handles out).
    { unfold handle_cells. rewrite a2. reflexivity. }
    assert (Hcounter : counter_allocation id p (countLN out allPieceIds) -|-
      counter_allocation freshid p (countLN out allPieceIds)).
    { unfold counter_allocation, payload_allocation. rewrite a2 a3 b0. reflexivity. }
    assert (Hcleanup : payload_releasable freshid Rnew -|- payload_releasable id Rnew).
    { unfold payload_releasable. rewrite a3 b0. reflexivity. }
    rewrite Hcells Hcounter.
    wapply (active_protocol freshid Rnew p out Hlive). go.
    wapply (inv_alloc nroot ⊤ (Exists actual, sptrInv freshid Rnew p actual)).
    rewrite <- fupd_intro. go.
    rewrite <- (bi.later_intro (Exists actual, sptrInv freshid Rnew p actual)).
    rewrite bi.sep_exist_r. iExists t. go.
    iExists freshid. go.
    wapply (census_close ty Rnew freshid p handles out). go.
    unfold protocol_knowledge. rewrite a3 Hcleanup.
    wapply Hdestruct. go.
  Qed.
End redistribution.

#[global] Hint Opaque allPiecesAndObjs : sl_opacity.
