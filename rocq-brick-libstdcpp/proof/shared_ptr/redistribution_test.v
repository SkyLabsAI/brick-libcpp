(** A genuinely different partition, not pointwise-equivalent pieces. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.shared_ptr.handle_liveness.
Require Import skylabs.brick.libstdcpp.shared_ptr.redistribution.

Set Default Goal Selector "!".
Import linearity.

Section tests.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Definition exchange_first_two (R : nat -> Rep) (i : nat) : Rep :=
    if decide (i = 0%nat) then R 1%nat else
    if decide (i = 1%nat) then R 0%nat else R i.

  Lemma exchange_first_two_whole R (p : ptr) :
    p |-> ([∗ list] i ∈ allPieceIds, R i) -|-
    p |-> ([∗ list] i ∈ allPieceIds, exchange_first_two R i).
  Proof.
    pose proof maxContentionLb as Hcap.
    assert (H0 : 0%nat ∈ allPieceIds) by (apply allPieceIds_member; lia).
    assert (H1 : 1%nat ∈ allPieceIds) by (apply allPieceIds_member; lia).
    assert (Hnd : NoDup allPieceIds) by (unfold allPieceIds; apply NoDup_seq).
    rewrite !_at_big_sepL.
    rewrite (big_op.big_sepL_difference_two (fun i => p |-> R i)
      allPieceIds 0%nat 1%nat ltac:(lia) H0 H1 Hnd).
    rewrite (big_op.big_sepL_difference_two (fun i => p |-> exchange_first_two R i)
      allPieceIds 0%nat 1%nat ltac:(lia) H0 H1 Hnd).
    assert (Hrest :
      ([∗ list] i ∈ list_difference allPieceIds [0%nat;1%nat], p |-> exchange_first_two R i)
      -|- ([∗ list] i ∈ list_difference allPieceIds [0%nat;1%nat], p |-> R i)).
    { apply big_sepL_proper. intros k i Hi.
      apply list_elem_of_lookup_2 in Hi. apply list_elem_of_difference in Hi.
      unfold exchange_first_two. rewrite !decide_False; set_solver. }
    rewrite Hrest. cbn [exchange_first_two].
    iSplit; unfold exchange_first_two; go.
  Qed.

  (** Ordinary scalar pieces satisfy the timelessness condition. *)
  Example int_partition_timeless id p q n :
    Timeless (Exists out, sptrInv id (fun _ => intR q n) p out).
  Proof.
    unfold sptrInv, pieceRight, pieceHandle, payload_allocation.
    destruct (payload_delete id) as [[op alignment]|];
      unfold SharedAllocationR; apply _.
  Qed.

End tests.

(** Use a concrete, equality-ordered index, with no growing thread view.
    Weak objectivity then follows for every assertion, including the library's
    abstract allocation tokens. For a non-discrete index the general theorem
    deliberately retains its explicit WeaklyObjective premise; the allocation
    interface does not currently provide that law. *)
Definition sc_index : biIndex := BiIndex unit _ eq _.

Section sc_test.
  Context {G : gFunctors} {Sigma : cpp_logic sc_index G} {CU : genv}.
  #[local] Existing Instance Sigma.

  #[local] Instance sc_index_symmetric : Symmetric (@sqsubseteq sc_index _).
  Proof. intros [] []. done. Qed.

  Definition one_int_piece (n : Z) (i : nat) : @Rep sc_index G Sigma :=
    if decide (i = 0%nat) then intR 1$m n else emp.

  Example move_int_piece id p handles out live n :
    live ∈ allPieceIds -> out live = true ->
    allPiecesAndObjs Tint (one_int_piece n) id p handles out |--
    |={⊤}=> Exists fresh : CtrlBlockId,
      [| dataLoc fresh = dataLoc id /\ payload_type fresh = payload_type id |] **
      allPiecesAndObjs Tint (exchange_first_two (one_int_piece n))
        fresh p handles out.
  Proof.
    intros Hlive Hout.
    eapply redistributePayloadOwnership with (live := live).
    { unfold sptrInv, pieceRight, pieceHandle, payload_allocation, one_int_piece.
      destruct (payload_delete id) as [[op alignment]|];
        unfold SharedAllocationR; apply _. }
    { intros. apply _. }
    { exact Hlive. }
    { exact Hout. }
    { apply exchange_first_two_whole. }
  Qed.
End sc_test.
