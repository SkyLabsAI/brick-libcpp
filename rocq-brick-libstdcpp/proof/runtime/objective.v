
Require Import skylabs.lang.cpp.logic.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.cpp.slice.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.iris.extra.proofmode.proofmode.

Module Type PROC_OBJECTIVE_AXIOM_TYPE.
Section proc_objective_axiom.
  Context `{Σ : !cpp_logic ti Σ0, σ : genv, !HasStdThreads Σ}.

  #[global] Declare Instance tptsto_pd_local_weakly_obj p ty q a :
      LocalWith procTI (tptsto ty q p a).
  #[global] Declare Instance padding_pd_local_weakly_obj q cls :
      LocalWithR procTI (structR cls q).
  #[global] Declare Instance mdc_path_pd_local_weakly_obj n path q p :
      LocalWith procTI (mdc_path n path q p).
  #[global] Declare Instance type_ptr_pd_local_weakly_obj p ty :
      LocalWith procTI (type_ptr ty p).
  #[global] Declare Instance valid_ptr_pd_local_weakly_obj p ty :
      LocalWith procTI (_valid_ptr ty p).
  #[global] Declare Instance anyR_pd_local_weakly_obj ty q :
      LocalWithR procTI (anyR ty q).
  #[global] Declare Instance has_type_pd_weakly_obj v ty :
      LocalWith procTI (has_type v ty).
End proc_objective_axiom.
End PROC_OBJECTIVE_AXIOM_TYPE.

Declare Module Export PROC_OBJECTIVE_AXIOM : PROC_OBJECTIVE_AXIOM_TYPE.

Section upstream.

  Context {PROP : bi}.
  Context {I J K : biIndex}.

  Lemma objective_of_obs {P : I -mon> PROP} Q :
    (Q -> Objective P) ->
    Observe [| Q |] P ->
    Objective P.
  Proof.
    move => HP /observe_monPred_at Hobs i j.
    iIntros "A"%string. iDestruct (Hobs with "A") as %?.
    by iStopProof; apply: HP.
  Qed.

  Section LocalWith.

    Lemma LocalWith_of_obs {P : I -mon> PROP} Q {L : I -ml> K} :
      (Q -> LocalWith L P) ->
      Observe [| Q |] P ->
      LocalWith L P.
    Proof.
      rewrite -!objective_local_with => HP Hobs j.
      apply objective_of_obs with (Q := Q), _ => HQ.
      by apply: HP.
    Qed.

    #[global] Instance LocalWith_only_provable P {L : I -ml> K} :
      LocalWith (PROP := PROP) L [| P |].
    Proof.
      rewrite -objective_local_with => ?.
      rewrite monPred_exactly_at_only_provable.
      apply _.
    Qed.

  End LocalWith.
  Section LocalWithR.

    Lemma LocalWithR_of_obs {P : J -mon> I -mon> PROP} Q {L : I -ml> K} :
      (Q -> LocalWithR L P) ->
      Observe [| Q |] P ->
      LocalWithR L P.
    Proof.
      rewrite !LocalWithR_monPred_at => HP Hobs p.
      eapply LocalWith_of_obs, _ => HQ.
      by apply: HP.
    Qed.

    #[global] Instance LocalWithR_only_provable P {L : I -ml> J} :
      LocalWithR (PROP := PROP) L [| P |].
    Proof.
      rewrite -objective_local_withR => ? ?.
      rewrite monPred_at_only_provable.
      rewrite monPred_exactly_at_only_provable.
      apply _.
    Qed.

  End LocalWithR.

End upstream.

Section derived_local_withR.
  Context `{Σ : !cpp_logic ti Σ0, σ : genv, !HasStdThreads Σ}.
  Implicit Types p : ptr.

  Section upstream.

    Lemma LocalWithR_iff_LocalWith_at (R : Rep) {J} {L : ti -ml> J} :
      LocalWithR L R <-> forall p, LocalWith L (p |-> R).
    Proof.
      rewrite -objective_local_withR; apply forall_proper => p.
      by rewrite !objective_local_with plogic.monPred_at_at.
    Qed.

    Lemma LocalWithR_iff_Objective_at (R : Rep) {J} {L : ti -ml> J} :
      LocalWithR L R <-> forall (p : ptr) i, Objective (@(L, i) p |-> R).
    Proof.
      rewrite -objective_local_withR; apply forall_proper => p.
      by rewrite !objective_local_with plogic.monPred_at_at.
    Qed.

    #[global] Instance LocalWithR_as_Rep (P : ptr -> mpred) {J} {L : ti -ml> J} :
      (forall p, LocalWith L (P p)) ->
      LocalWithR L (as_Rep P).
    Proof.
      rewrite LocalWithR_iff_LocalWith_at => Hp p.
      by rewrite _at_as_Rep.
    Qed.

    Section LocalWith.

      #[global] Instance LocalWith_at (R : Rep) {J} {L : ti -ml> J} :
        LocalWithR L R -> forall p, LocalWith L (p |-> R).
      Proof. rewrite LocalWithR_iff_LocalWith_at; apply _. Qed.

    End LocalWith.

    Section LocalWithR.

      #[global] Instance LocalWithR_offsetR (R : Rep) {J} {L : ti -ml> J} :
        LocalWithR L R -> forall o : offset, LocalWithR L (o |-> R).
      Proof.
        rewrite LocalWithR_iff_LocalWith_at => HR o.
        rewrite LocalWithR_iff_LocalWith_at => p.
        by rewrite _at_offsetR.
      Qed.

    End LocalWithR.

  End upstream.

  #[global] Instance validR_pd_local_obj :
    LocalWithR procTI validR.
  Proof.
    rewrite LocalWithR_iff_LocalWith_at => p.
    rewrite _at_validR; apply _.
  Qed.

  #[global] Instance tptstoR_pd_local_obj ty q v :
    LocalWithR procTI (tptstoR ty q v).
  Proof.
    rewrite LocalWithR_iff_LocalWith_at => p.
    rewrite _at_tptstoR; apply _.
  Qed.

  #[global] Instance tptsto_fuzzyR_pd_local_obj ty q v :
    LocalWithR procTI (tptsto_fuzzyR ty q v).
  Proof.
    rewrite LocalWithR_iff_LocalWith_at => p.
    rewrite _at_tptsto_fuzzyR; apply _.
  Qed.

  #[global] Instance primR_pd_local_obj ty q v :
    LocalWithR procTI (primR ty q v).
  Proof.
    rewrite LocalWithR_iff_LocalWith_at => p.
    rewrite _at_primR; apply _.
  Qed.

  #[global] Instance uninitR_pd_local_obj ty q :
    LocalWithR procTI (uninitR ty q).
  Proof. rewrite uninitR.unlock; apply _. Qed.

  #[global] Instance type_ptrR_pd_local_obj ty :
    LocalWithR procTI (type_ptrR ty).
  Proof. rewrite type_ptrR_eq /type_ptrR_def. apply _. Qed.

  #[global] Instance derivationR_pd_local_obj n path q :
    LocalWithR procTI (derivationR n path q).
  Proof. rewrite derivationR.unlock. apply _. Qed.

  (** TODO: allow references to list in assumptions:
      << (∀ i x, xs !! i = Some x -> LocalWithR procTI (Rs x)) >>
   *)
  Lemma arrayR_pd_local_obj_lookup
    {X} ty (Rs : X → Rep) (xs : list X) :
    (∀ x, LocalWithR procTI (Rs x)) →
    LocalWithR procTI (arrayR ty Rs xs).
  Proof.
    intros HRs.
    rewrite arrayR_eq /arrayR_def arrR_eq /arrR_def.
    repeat first [ apply sep_local_withR | apply _ ].
    rewrite big_opL_fmap.
    apply _.
  Qed.

  (** TODO: allow references to list in assumptions:
      << (∀ i x, xs !! i = Some x -> LocalWithR procTI (Rs x)) >>
   *)
  Lemma array_sliceR_pd_local_obj_lookup m n
    {X} ty (Rs : X → Rep) (xs : list X) :
    (∀ x, LocalWithR procTI (Rs x)) →
    LocalWithR procTI (array_sliceR ty m n Rs xs).
  Proof.
    intros HR.
    rewrite array_sliceR.unlock.
    apply sep_local_withR; first apply _.
    apply LocalWithR_offsetR, arrayR_pd_local_obj_lookup => x.
    apply _.
  Qed.

  #[global] Instance arrayR_pd_local_obj
    {X} ty (Rs : X → Rep) (xs : list X)
    `{∀ (x : X), LocalWithR procTI (Rs x)} :
    LocalWithR procTI (arrayR ty Rs xs).
  Proof. by apply arrayR_pd_local_obj_lookup, _. Qed.

  #[global] Instance array_sliceR_pd_local_obj
    {X} ty (Rs : X → Rep) (xs : list X) m n
    `{∀ (x : X), LocalWithR procTI (Rs x)} :
    LocalWithR procTI (array_sliceR ty m n Rs xs).
  Proof. by apply array_sliceR_pd_local_obj_lookup, _. Qed.

End derived_local_withR.
