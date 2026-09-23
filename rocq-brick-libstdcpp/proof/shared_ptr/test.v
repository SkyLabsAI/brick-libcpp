Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.stdlib.allocator.spec.
Require Import skylabs.cpp.stdlib.cassert.spec.
Require Import skylabs.cpp.stdlib.vector.spec.
Require Import skylabs.cpp.stdlib.atomic.spec.
Require Import skylabs.cpp.stdlib.algorithms.spec.
Require Import skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.new.spec_exc.
Require Import skylabs.brick.libstdcpp.new.hints.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.
Require Import skylabs.brick.libstdcpp.shared_ptr.test_cpp.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.


(* TODO: upstream the hints/lemmas, to where? *)
Hint Resolve NoDup_seq : setsolver.
Hint Rewrite elem_of_seq: equiv.
Hint Rewrite @big_sepL_emp: equiv.

Lemma seqprefix (prelen len start: nat):
  (prelen <= len)%nat -> seq start len = (seq start prelen)++(seq (start+prelen) (len -prelen)).
Proof using.
  intros Hl.
  replace len with (prelen+(len-prelen))%nat at 1 by lia.
  rewrite seq_app.
  reflexivity.
Qed.
  
Lemma one_as_bigsep {PROP: bi} {A} {eqd: EqDecision A} (f  : PROP) l (x: A):
  x ∈ l ->
  NoDup l -> (* too strong: we only need x to be not duplicated *)
  f -|- ([∗ list] id ∈ l, if bool_decide (id=x) then f else emp)%I.
Proof using.
  intros.
  rewrite  -> big_op.big_sepL_difference_singleton with (x:=x) by assumption.
  simpl.
  case_bool_decide; [ | congruence].
  assert (f ** (emp)%I ≡ f) as Heq by (apply right_id; eauto with typeclass_instances).
  rewrite <- Heq at 1.
  f_equiv.
  transitivity ([∗ list] _ ∈ list_difference l [x], (emp : PROP))%I.
  { symmetry. apply big_sepL_emp. }
  apply big_opL_proper.
  intros  ? id  Hl.
  case_decide;[ | reflexivity].
  subst.
  apply list_elem_of_lookup_2 in Hl.
  apply list_elem_of_difference in Hl.
  forward_reason.
  apply False_rect.
  simpl in *.
  set_solver.
Qed.

Section proofs.
  #[local] Set Warnings "-sl-transparent-constants".
  Opaque SharedPtrR.
  Context `{Σ : cpp_logic, MOD:test_cpp.source ⊧ σ}
  {hf:fracG () _Σ}.
  

  cpp.spec "testshared1()" as testshared1spec with (
    \pre emp
    \post{p:ptr}[Vptr p] Exists payload sid,
       [| payload_type sid = "int"%cpp_type |] **
       p |-> SharedPtrR "int" 1$m sid 0 (fun ctid => if bool_decide (ctid=0%nat) then anyR "int" 1 else emp) payload
       ** payload |-> intR (cQp.m 1) 1
       ** ([∗ list] ctid ∈ allButFirstPieceId,
              pieceRight sid ctid)
    ).



  Lemma allButFirstEmp ty : ([∗ list] x ∈ seq 1 (Pos.to_nat maxContention -1), 
       if bool_decide (x = 0%nat)
       then anyR ty 1$m
       else emp)
                         -|- emp.
  Proof using.
    erewrite  big_opL_proper with (g := fun _ _=> emp).
    2:{ intros ? ? Hl.
        apply list_elem_of_lookup_2 in Hl.
        autorewrite with equiv in Hl.
        resolveDecide lia.
        reflexivity.
    }
    autorewrite with equiv.
    reflexivity.
  Qed.
  
  Opaque NullSharedPtrR.
  #[global] Instance lll: LearnEq6 SharedPtrR :=
    ltac:(solve_learnable).

Set Default Goal Selector "!".  
  Lemma prf2: verify[source] testshared1spec.
  Proof using MOD.
    verify_spec.
    pose proof maxContentionLb.
    go.
    let r := sharedPtrRpieceFromPost in
      set (Rpiece := r).
    iExists Rpiece.
    go.
    simpl.
    eagerUnifyU.
    go.
    normalize_ptrs.
    eagerUnifyU.
    go.
    rewrite <- _at_big_sepL.
    unfold allButFirstPieceId.
    rewrite allButFirstEmp. go.
    assert (Hdestroy : emp |-- payload_destructible "int" Rpiece).
    {
      unfold Rpiece.
      unfold payload_destructible, allPieceIds.
      rewrite -> seqprefix with (prelen:=1%nat) by lia.
      simpl.
      setoid_rewrite (allButFirstEmp "int"). go.
      rewrite destroy_val_wp_destroy_val.
      go.
    }
    rewrite <- Hdestroy.
    go.
    normalize_ptrs.
    go.
    normalize_ptrs.
    repeat iExists _.
    eagerUnifyC.
    go.
    iExists true.
    go.
    iExists nullptr.
    iExists tt.
    iExists (fun _ => emp).
    go.
  Qed.

  (* dummy spec: needs fix *)
  cpp.spec "testsharedarr()" as testsharedarrspec with (
    \pre emp
    \post{p:ptr}[Vptr p] Exists payload sid,
       [| payload_type sid = "int[2]"%cpp_type |] **
       p |-> SharedPtrR "int[]" 1$m sid 0 (fun ctid => if bool_decide (ctid=0%nat) then anyR "int[2]" 1 else emp) payload
       ** payload |-> arrayR "int" (fun t => intR 1 t) [1;2]%Z
       ** ([∗ list] ctid ∈ allButFirstPieceId,
              pieceRight sid ctid)
      ).

  
  Lemma prf3: (SIZE_MAX = 2^64)%N -> verify[source] testsharedarrspec.
  Proof using MOD.
    verify_spec.
    go;[lia|].
    let r := sharedPtrRpieceFromPost in
      set (Rpiece := r).
    iExists Rpiece.
    go.
    simpl.
    eagerUnifyU.
    go.
    normalize_ptrs.
    ring_simplify_goal_Z.
    normalize_ptrs.
    go.
    eagerUnifyU.
    go.
    rewrite <- _at_big_sepL.
    unfold allButFirstPieceId.
    rewrite allButFirstEmp. go.
    assert (Hdestroy : emp |-- payload_destructible "int[2]" Rpiece).
    {
      unfold Rpiece.
      unfold payload_destructible, allPieceIds.
      rewrite -> seqprefix with (prelen:=1%nat) by lia.
      simpl.
      setoid_rewrite (allButFirstEmp "int[2]").
      go.
      rewrite destroy_val_wp_destroy_val.
      go.
    }
    rewrite <- Hdestroy.
    go.
    normalize_ptrs.
    go.
    normalize_ptrs.
    go.
    simpl.
    unfold replicateN.
    simpl.
    repeat rewrite arrayR_cons.
    go.
    normalize_ptrs.
    go.
    normalize_ptrs.
    go.
    iExists true.
    go.
    iExists nullptr.
    iExists tt.
    iExists (fun _ => emp).
    go.
    (* TODO: proof needs rework after alloc.tokenR transition. *)
    repeat rewrite arrayR_cons.
    go.
    normalize_ptrs.
    go.
    repeat rewrite arrayR_nil.
    go.
  Qed.
End proofs.
