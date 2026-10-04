
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
      WeaklyLocalWith procTI (tptsto ty q p a).
  #[global] Declare Instance padding_pd_local_weakly_obj q cls :
      WeaklyLocalWithR procTI (structR cls q).
  #[global] Declare Instance mdc_path_pd_local_weakly_obj n path q p :
      WeaklyLocalWith procTI (mdc_path n path q p).
  #[global] Declare Instance type_ptr_pd_local_weakly_obj p ty :
      WeaklyLocalWith procTI (type_ptr ty p).
  #[global] Declare Instance valid_ptr_pd_local_weakly_obj p ty :
      WeaklyLocalWith procTI (_valid_ptr ty p).
  #[global] Declare Instance anyR_pd_local_weakly_obj ty q :
      WeaklyLocalWithR procTI (anyR ty q).
  #[global] Declare Instance has_type_pd_weakly_obj v ty :
      WeaklyLocalWith procTI (has_type v ty).
End proc_objective_axiom.
End PROC_OBJECTIVE_AXIOM_TYPE.

Declare Module Export PROC_OBJECTIVE_AXIOM : PROC_OBJECTIVE_AXIOM_TYPE.

Section upstream.

  Lemma weakly_objective_of_obs {ix} {PROP : bi} {P : ix -mon> PROP} Q :
    (Q -> WeaklyObjective P) ->
    Observe [| Q |] P ->
    WeaklyObjective P.
  Proof.
    move => HP /observe_monPred_at Hobs i j Hij.
    iIntros "A"%string. iDestruct (Hobs with "A") as %?.
    by iStopProof; apply: HP.
  Qed.

  Lemma weakly_objectiveR_of_obs {ix jx} {PROP : bi} {P : ix -mon> jx -mon> PROP} Q :
    (Q -> WeaklyObjectiveR P) ->
    Observe [| Q |] P ->
    WeaklyObjectiveR P.
  Proof.
    rewrite !WeaklyObjectiveR_monPred_at => HP Hobs p.
    eapply weakly_objective_of_obs, _ => HQ.
    by apply: HP.
  Qed.

  Lemma weakly_local_of_obs {ix jx} {PROP : bi} {P : ix -mon> PROP} Q (L : ix -ml> jx) :
    (Q -> WeaklyLocalWith L P) ->
    Observe [| Q |] P ->
    WeaklyLocalWith L P.
  Proof.
    rewrite -!weakly_objective_weakly_local_with => HP Hobs j.
    apply weakly_objective_of_obs with (Q := Q), _ => HQ.
    by apply: HP.
  Qed.

  Lemma weakly_localR_of_obs {ix jx kx} {PROP : bi} {P : ix -mon> jx -mon> PROP} Q (L : jx -ml> kx) :
    (Q -> WeaklyLocalWithR L P) ->
    Observe [| Q |] P ->
    WeaklyLocalWithR L P.
  Proof.
    rewrite !WeaklyLocalWithR_monPred_at => HP Hobs p.
    eapply weakly_local_of_obs, _ => HQ.
    by apply: HP.
  Qed.

End upstream.

Section derived_pd_local_weakly_local_withR.
  Context `{Σ : !cpp_logic ti Σ0, σ : genv, !HasStdThreads Σ}.

  Lemma WeaklyLocalWithR_iff_WeaklyObjective_at (R : Rep) :
    WeaklyLocalWithR procTI R <-> forall (p : ptr) pd, WeaklyObjective (@(procTI, pd) p |-> R).
  Proof.
    rewrite WeaklyLocalWithR_iff_WeaklyLocalWith_at; apply forall_proper => p.
    by rewrite -weakly_objective_weakly_local_with.
  Qed.

  #[global] Instance validR_pd_local_weakly_obj :
    WeaklyLocalWithR procTI validR.
  Proof. rewrite validR_eq /validR_def /=. apply _. Qed.

  #[global] Instance tptstoR_pd_local_weakly_obj ty q v :
    WeaklyLocalWithR procTI (tptstoR ty q v).
  Proof.
    rewrite WeaklyLocalWithR_iff_WeaklyLocalWith_at => p.
    rewrite _at_tptstoR; apply _.
  Qed.

  #[global] Instance tptsto_fuzzyR_pd_local_weakly_obj ty q v :
    WeaklyLocalWithR procTI (tptsto_fuzzyR ty q v).
  Proof.
    rewrite WeaklyLocalWithR_iff_WeaklyLocalWith_at => p.
    rewrite _at_tptsto_fuzzyR; apply _.
  Qed.

  #[global] Instance primR_pd_local_weakly_obj ty q v :
    WeaklyLocalWithR procTI (primR ty q v).
  Proof.
    rewrite WeaklyLocalWithR_iff_WeaklyLocalWith_at => p.
    rewrite _at_primR; apply _.
  Qed.

  #[global] Instance uninitR_pd_local_weakly_obj ty q :
    WeaklyLocalWithR procTI (uninitR ty q).
  Proof. rewrite uninitR.unlock; apply _. Qed.

  #[global] Instance type_ptrR_pd_local_weakly_obj ty :
    WeaklyLocalWithR procTI (type_ptrR ty).
  Proof. rewrite type_ptrR_eq /type_ptrR_def; apply _. Qed.

  #[global] Instance derivationR_pd_local_weakly_obj n path q :
    WeaklyLocalWithR procTI (derivationR n path q).
  Proof. rewrite derivationR.unlock. apply _. Qed.

  Lemma arrayR_pd_local_weakly_obj_lookup
    {X} ty (Rs : X → Rep) (xs : list X) :
    (∀ n x, xs !! n = Some x →
            WeaklyLocalWithR procTI ((.[ ty ! n ]) |-> Rs x)) →
    WeaklyLocalWithR procTI (arrayR ty Rs xs).
  Proof.
    intros HRs.
    rewrite arrayR_eq /arrayR_def arrR_eq /arrR_def.
    repeat first [ apply sep_weakly_local_withR | apply _ ].
    apply big_sepL_weakly_local_withR_lookup => n R.
    rewrite list_lookup_fmap fmap_Some _offsetR_sep => - [x] [Hx ->].
    apply sep_weakly_local_withR, HRs; [apply _ | ].
    rewrite lookupZ_Some_to_nat !Nat2Z.id.
    by split; first lia.
  Qed.

  Lemma array_sliceR_pd_local_weakly_obj_lookup m n
    {X} ty (Rs : X → Rep) (xs : list X) :
    (∀ i x, xs !! i = Some x →
            (0 ≤ i < n - m)%Z ->
            WeaklyLocalWithR procTI ((.[ ty ! i ]) |-> Rs x)) →
    WeaklyLocalWithR procTI (array_sliceR ty m n Rs xs).
  Proof.
    intros HR.
    apply weakly_localR_of_obs with (Q := lengthZ xs = (n - m)%Z), _ => Hlen.
    rewrite array_sliceR.unlock.
    apply sep_weakly_local_withR; first apply _.
    apply WeaklyLocalWithR_offsetR, arrayR_pd_local_weakly_obj_lookup => i x Hix.
    have ? := lookupZ_Some Hix.
    by apply HR; last lia.
  Qed.

  #[global] Instance arrayR_pd_local_weakly_obj
    {X} ty (Rs : X → Rep) (xs : list X)
    `{∀ (x : X), WeaklyLocalWithR procTI (Rs x)} :
    WeaklyLocalWithR procTI (arrayR ty Rs xs).
  Proof. by apply arrayR_pd_local_weakly_obj_lookup, _. Qed.

  #[global] Instance array_sliceR_pd_local_weakly_obj
    {X} ty (Rs : X → Rep) (xs : list X) m n
    `{∀ (x : X), WeaklyLocalWithR procTI (Rs x)} :
    WeaklyLocalWithR procTI (array_sliceR ty m n Rs xs).
  Proof. by apply array_sliceR_pd_local_weakly_obj_lookup, _. Qed.

End derived_pd_local_weakly_local_withR.
