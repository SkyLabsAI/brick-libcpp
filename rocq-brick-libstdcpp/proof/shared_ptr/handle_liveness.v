(** The indexed handle token has two jobs: identify the payload piece required
    at destruction, and exclude a released control block while any fraction
    of a handle remains live. These are representation lemmas, independent of
    the assumed C++ library method specs. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.

Set Default Goal Selector "!".
Import linearity observe2_fwd.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.
  #[local] Existing Instance br.ghost.frac_inG.
  #[local] Hint Opaque pieceHandle pieceRight SharedPtrR sptrInv
    payload_destructible : sl_opacity.

  Lemma pieceHandle_full_conflict id q i :
    pieceHandle id q i ** pieceHandle id 1 i |-- False.
  Proof.
    unfold pieceHandle.
    destruct (nth_error (pieceHandleLocs id) i) as [name |].
    {
      rewrite <- own_op, own_valid, algebra.discrete_validI.
      apply bi.pure_mono.
      exact (Qp.not_add_le_r q 1).
    }
    { go. }
  Qed.

  #[local] Definition pieceHandle_full_conflict_F :=
    [FWD] pieceHandle_full_conflict.

  (* An available slot owns the full token inside the invariant. Hence even
     read-only fractional ownership of a handle excludes that state. *)
  Lemma pieceHandle_outstanding id q i Rpiece owned pieceOut :
    i ∈ allPieceIds ->
    pieceHandle id q i ** sptrInv id Rpiece owned pieceOut
    |-- [| pieceOut i = true |] **
        pieceHandle id q i ** sptrInv id Rpiece owned pieceOut.
  Proof.
    intros Hi.
    destruct (pieceOut i) eqn:Hout.
    { go. }
    unfold sptrInv.
    rewrite -> big_op.big_sepL_difference_singleton with (x := i).
    2: { exact Hi. }
    2: { unfold allPieceIds. apply NoDup_seq. }
    rewrite Hout.
    go using pieceHandle_full_conflict_F.
  Qed.

  Lemma countLN_positive_of_member {A} (f : A -> bool) l i :
    i ∈ l -> f i = true -> (0 < countLN f l)%N.
  Proof.
    intros Hi Hout.
    assert (Hin : i ∈ filter f l).
    {
      apply list_elem_of_filter. split.
      { by rewrite Hout. }
      { exact Hi. }
    }
    unfold countLN.
    destruct (filter f l) as [| head rest].
    { inversion Hin. }
    { unfold lengthN. simpl. lia. }
  Qed.

  Lemma pieceHandle_live id q i Rpiece owned pieceOut :
    i ∈ allPieceIds ->
    pieceHandle id q i ** sptrInv id Rpiece owned pieceOut
    |-- [| (0 < countLN pieceOut allPieceIds)%N |] **
        pieceHandle id q i ** sptrInv id Rpiece owned pieceOut.
  Proof.
    intros Hi.
    etrans.
    { exact (pieceHandle_outstanding id q i Rpiece owned pieceOut Hi). }
    go using countLN_positive_of_member.
  Qed.

  #[local] Lemma pieceHandle_live_observe id q i Rpiece owned pieceOut :
    i ∈ allPieceIds ->
    Observe2 [| (0 < countLN pieceOut allPieceIds)%N |]
      (pieceHandle id q i) (sptrInv id Rpiece owned pieceOut).
  Proof.
    intros Hi.
    apply observe_2_intro.
    { apply _. }
    apply bi.wand_intro_r.
    etrans.
    { exact (pieceHandle_live id q i Rpiece owned pieceOut Hi). }
    go.
  Qed.
  #[local] Definition pieceHandle_live_F :=
    ltac:(mk_obs2_fwd pieceHandle_live_observe).

  Lemma allPieceIds_member i :
    (N.of_nat i < N.pos maxContention)%N -> i ∈ allPieceIds.
  Proof.
    unfold allPieceIds. rewrite elem_of_seq. lia.
  Qed.
  #[local] Hint Resolve allPieceIds_member : pure.

  Lemma SharedPtrR_live ty q id i Rpiece owned (handle : ptr) pieceOut :
    handle |-> SharedPtrR ty q id i Rpiece owned **
    sptrInv id Rpiece owned pieceOut
    |-- [| (0 < countLN pieceOut allPieceIds)%N |] **
        handle |-> SharedPtrR ty q id i Rpiece owned **
        sptrInv id Rpiece owned pieceOut.
  Proof.
    unfold SharedPtrR.
    go using pieceHandle_live_F.
  Qed.
End with_cpp.
