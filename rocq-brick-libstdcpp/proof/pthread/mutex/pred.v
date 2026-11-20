(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.mutex.model.
Require Import iris.algebra.lib.excl_auth.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.auto.cpp.local_with.
Require Import skylabs.brick.libstdcpp.runtime.objective.
Require Import skylabs.iris.extra.base_logic.monpred_invariants.
Require Import skylabs.iris.extra.base_logic.monpred_own.
Require Import skylabs.iris.extra.bi.cancelable_invariants.
Require Import skylabs.iris.extra.base_logic.iprop_invariants.

(* Clients can use the laws below while the invariant's representation and
   provider updates stay inside the sealed module. *)
Module Type PTHREAD_MUTEX_PROTOCOL.
  Local Abbreviation stateR := (excl_authR mutex_stateO).

  Parameter mutex_available :
    forall `{Σ : @cpp_logic thread_info _Σ} {σ : genv}, ptr -> mpred.
  Parameter mutex_live :
    forall `{Σ : @cpp_logic thread_info _Σ} {σ : genv} `{!HasOwn (iPropI _Σ) stateR},
      ptr -> mutex_generation -> mpred -> mpred.
  Parameter mutex_access :
    forall `{Σ : @cpp_logic thread_info _Σ}, mutex_generation -> Qp -> mpred.
  Parameter mutex_held :
    forall `{Σ : @cpp_logic thread_info _Σ} `{!HasOwn (iPropI _Σ) stateR},
      mutex_generation -> thread_idT -> Qp -> mpred.
  Parameter mutex_ready :
    forall `{Σ : @cpp_logic thread_info _Σ} {σ : genv} `{!HasOwn (iPropI _Σ) stateR},
      ptr -> mpred -> mpred.
  Parameter mutex_owned :
    forall `{Σ : @cpp_logic thread_info _Σ} `{!HasOwn (iPropI _Σ) stateR} {threads : HasStdThreads Σ},
      mutex_generation -> thread_idT -> Qp -> mpred.

Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.
  Context `{!HasOwn (iPropI _Σ) stateR}.

  Parameter mutex_live_persistent : forall p g P, Persistent (mutex_live p g P).
  Parameter mutex_access_fractional : forall g, Fractional (mutex_access g).
  Parameter mutex_access_split : forall g q1 q2,
    mutex_access g (q1 + q2)%Qp -|- mutex_access g q1 ** mutex_access g q2.
  Parameter mutex_available_from_uninitialized : forall (p : ptr),
    p |-> uninitR "pthread_mutex_t" 1$m |-- mutex_available p.
  Parameter mutex_held_exclusive :
    forall `{state_valid : !HasOwnValid (iPropI _Σ) stateR} g owner1 owner2 q1 q2,
      mutex_held g owner1 q1 ** mutex_held g owner2 q2 |-- False.
  Parameter mutex_full_excludes_access : forall g q,
    mutex_access g 1%Qp ** mutex_access g q |-- False.
  Parameter mutex_full_excludes_held : forall g owner q,
    mutex_access g 1%Qp ** mutex_held g owner q |-- False.
  Parameter mutex_ready_open : forall p P,
    mutex_ready p P -|- ∃ g, mutex_live p g P ** mutex_access g 1%Qp.

  Context {threads : HasStdThreads Σ}.

  Parameter mutex_owned_open : forall g owner q,
    mutex_owned g owner q -|- current_thread owner ** mutex_held g owner q.
  Parameter mutex_access_process_local : forall g q,
    LocalWith procTI (mutex_access g q).
  Parameter mutex_available_process_local : forall (p : ptr),
    LocalWith procTI (mutex_available p).
  Parameter mutex_live_process_local : forall p g P,
    LocalWith procTI P -> LocalWith procTI (mutex_live p g P).
End with_cpp.
End PTHREAD_MUTEX_PROTOCOL.

Module Protocol : PTHREAD_MUTEX_PROTOCOL.
Section with_cpp.
  Context `{Σ : @cpp_logic thread_info _Σ} {σ : genv}.
  Local Instance mutex_cinvG : cinvFracG _Σ.
  Proof using Σ. constructor; apply _. Defined.

  Local Abbreviation stateR := (excl_authR mutex_stateO).
  Context `{!HasOwn (iPropI _Σ) stateR}.

  (* Exclusive available storage before initialization or after destruction. *)
  Definition mutex_available (p : ptr) : mpred :=
    p |-> anyR "pthread_mutex_t" 1$m.

  Local Definition mutex_body (p : ptr) (g : mutex_generation) (P : mpred) : mpred :=
    mutex_available p **
    ∃ s : mutex_state, own g.(mutex_state_name) (●E s) **
      match s with
      | MutexUnlocked => own g.(mutex_state_name) (◯E MutexUnlocked) ** P
      | MutexLocked _ q => cinv_own g.(mutex_lifetime_name) (q / 2)%Qp
      end.

  (* Handle metadata can be shared. All concrete mutex storage stays inside
     the invariant until safe destruction. *)
  Definition mutex_live (p : ptr) (g : mutex_generation) (P : mpred) : mpred :=
    cinv (mutex_namespace g) g.(mutex_lifetime_name) (mutex_body p g P).

  (* A caller or waiter must retain an access fraction. *)
  Definition mutex_access (g : mutex_generation) (q : Qp) : mpred :=
    cinv_own g.(mutex_lifetime_name) q.

  (* The other half of this loan is in the invariant until release. Unlock
     pairs this exclusive token with the installed [current_thread owner]. *)
  Definition mutex_held (g : mutex_generation) (owner : thread_idT) (q : Qp) : mpred :=
    own g.(mutex_state_name) (◯E (MutexLocked owner q)) **
    cinv_own g.(mutex_lifetime_name) (q / 2)%Qp.

  #[global] Instance mutex_live_persistent p g P : Persistent (mutex_live p g P).
  Proof. rewrite /mutex_live. apply _. Qed.

  #[global] Instance mutex_access_fractional g : Fractional (mutex_access g).
  Proof. intro q1; intro q2. rewrite !/mutex_access. apply (fractional _). Qed.

  Lemma mutex_access_split g q1 q2 :
    mutex_access g (q1 + q2)%Qp -|- mutex_access g q1 ** mutex_access g q2.
  Proof. apply (fractional _). Qed.

  Lemma mutex_available_from_uninitialized (p : ptr) :
    p |-> uninitR "pthread_mutex_t" 1$m |-- mutex_available p.
  Proof. by rewrite /mutex_available uninitR_anyR. Qed.

  Context `{state_valid : !HasOwnValid (iPropI _Σ) stateR}.

  Lemma mutex_held_exclusive g owner1 owner2 q1 q2 :
    mutex_held g owner1 q1 ** mutex_held g owner2 q2 |-- False.
  Proof using state_valid.
    rewrite !/mutex_held.
    iIntros "[[H1 _] [H2 _]]".
    iDestruct (own_valid_2 with "H1 H2") as %H.
    by apply excl_auth_frag_op_valid in H.
  Qed.

  Lemma mutex_full_excludes_access g q :
    mutex_access g 1%Qp ** mutex_access g q |-- False.
  Proof.
    rewrite !/mutex_access.
    iIntros "[H1 H2]".
    by iDestruct (cinv_own_1_l with "H1 H2") as %[].
  Qed.

  Lemma mutex_full_excludes_held g owner q :
    mutex_access g 1%Qp ** mutex_held g owner q |-- False.
  Proof.
    rewrite /mutex_access /mutex_held.
    iIntros "[H1 [_ H2]]".
    by iDestruct (cinv_own_1_l with "H1 H2") as %[].
  Qed.

  (* Both initialization routes hand off this same initially unlocked resource. *)
  Definition mutex_ready (p : ptr) (P : mpred) : mpred :=
    ∃ g, mutex_live p g P ** mutex_access g 1%Qp.

  Lemma mutex_ready_open p P :
    mutex_ready p P -|- ∃ g, mutex_live p g P ** mutex_access g 1%Qp.
  Proof. reflexivity. Qed.

  Context `{can_allocate : !HasOwnUpd mpredI stateR}.
  Context {threads : HasStdThreads Σ}.

  Definition mutex_owned (g : mutex_generation) (owner : thread_idT) (q : Qp) : mpred :=
    current_thread owner ** mutex_held g owner q.

  Lemma mutex_owned_open g owner q :
    mutex_owned g owner q -|- current_thread owner ** mutex_held g owner q.
  Proof. reflexivity. Qed.

  Lemma mutex_access_process_local g q :
    LocalWith procTI (mutex_access g q).
  Proof.
    intros i j _.
    rewrite /mutex_access /cinv_own /own has_own_monpred_eq /has_own_monpred_def !monPred_at_embed.
    reflexivity.
  Qed.

  Lemma mutex_available_process_local (p : ptr) :
    LocalWith procTI (mutex_available p).
  Proof.
    rewrite /mutex_available.
    pose proof (anyR_pd_local_weakly_obj "pthread_mutex_t" (1$m)) as Hlocal.
    rewrite LocalWithR_iff_LocalWith_at in Hlocal.
    exact (Hlocal p).
  Qed.

  Local Lemma mutex_state_process_local name (state : stateR) :
    LocalWith procTI (own (PROP := mpredI) name state).
  Proof.
    intros i j _.
    rewrite /own has_own_monpred_eq /has_own_monpred_def !monPred_at_embed.
    reflexivity.
  Qed.

  Lemma mutex_live_process_local p g P :
    LocalWith procTI P -> LocalWith procTI (mutex_live p g P).
  Proof.
    intros HP.
    assert (Hbody : LocalWith procTI (mutex_body p g P)).
    {
      rewrite /mutex_body.
      apply sep_local_with; first apply mutex_available_process_local.
      apply exist_local_with. intros [|owner loan].
      - apply sep_local_with; first apply mutex_state_process_local.
        apply sep_local_with; [apply mutex_state_process_local | exact HP].
      - apply sep_local_with; first apply mutex_state_process_local.
        apply (mutex_access_process_local g (loan / 2)%Qp).
    }
    assert (Hcancel :
      LocalWith procTI (mutex_body p g P ∨ cinv_own g.(mutex_lifetime_name) 1%Qp)).
    { apply or_local_with; [exact Hbody | apply (mutex_access_process_local g 1%Qp)]. }
    rewrite /mutex_live /cinv inv_eq /inv_def.
    typeclasses eauto.
  Qed.

  Local Lemma mutex_available_objective p :
    WeaklyObjective (mutex_available p).
  Proof using threads.
    intros i j Hji.
    apply (mutex_available_process_local p).
    symmetry. exact (mlens_get_mono procTI _ _ Hji).
  Qed.

  (* Provider-side construction after actual initialization. Kept private so
     possession of raw storage cannot stand in for a successful API operation. *)
  Local Lemma mutex_install E p P :
    WeaklyObjective P ->
    mutex_available p ** ▷ P |-- |={E}=> mutex_ready p P.
  Proof using can_allocate threads.
    iIntros (Hobjective) "[Hstorage HP]".
    iMod (own_alloc (●E MutexUnlocked ⋅ ◯E MutexUnlocked)) as (state) "[Hauth Hfrag]".
    { apply excl_auth_valid. }
    set (N := mutex_namespace {| mutex_state_name := state;
                                mutex_lifetime_name := state |}).
    iMod (monpred_invariants.cinv_alloc_cofinite ∅ E N) as (life _) "[Hshare Halloc]".
    set (g := {| mutex_state_name := state; mutex_lifetime_name := life |}).
    assert (HbodyObjective : WeaklyObjective (mutex_body p g P)).
    {
      rewrite /mutex_body.
      apply sep_weakly_objective; first apply mutex_available_objective.
      apply exists_weakly_objective.
      intros [|owner loan]; apply sep_weakly_objective; try apply _.
      rewrite /cinv_own. apply _.
    }
    iAssert (▷ mutex_body p g P)%I with "[Hstorage HP Hauth Hfrag]" as "Hbody".
    { rewrite /mutex_body. iNext. iFrame "Hstorage". iExists MutexUnlocked. simpl. iFrame. }
    iMod ("Halloc" $! (mutex_body p g P) HbodyObjective with "Hbody") as "Hinv".
    iModIntro. rewrite /mutex_ready. iExists g. rewrite /mutex_live /mutex_access. iFrame "Hshare". iExact "Hinv".
  Qed.

  (* Provider-side cancellation. The destroy contract retires this generation
     when the real call ends the physical mutex lifetime. *)
  Local Lemma mutex_cancel E p g P :
    ↑(mutex_namespace g) ⊆ E ->
    mutex_live p g P ** mutex_access g 1%Qp |-- |={E}=> ▷ (mutex_available p ** P).
  Proof.
    iIntros (Hmask) "[#Hinv Hfull]".
    rewrite /mutex_live /mutex_access.
    iMod (cinv_acc_strong with "Hinv Hfull") as "(Hbody & Hfull & Hclose)"; first done.
    rewrite /mutex_body.
    iDestruct "Hbody" as "(Hstorage & Hstate)".
    iDestruct "Hstate" as (s) "[Hauth Hstate]".
    destruct s as [|owner loan].
    - iDestruct "Hstate" as "[Hfrag HP]".
      rewrite {2}(union_difference_L (↑(mutex_namespace g)) E) //.
      iMod ("Hclose" with "[Hfull]") as "_"; first by iRight.
      iModIntro. iNext. iFrame.
    - iMod "Hstate" as "Hloan".
      by iDestruct (cinv_own_1_l with "Hfull Hloan") as %[].
  Qed.
End with_cpp.

End Protocol.
Export Protocol.

#[global] Existing Instance mutex_live_persistent.
#[global] Existing Instance mutex_access_fractional.
#[global] Hint Opaque mutex_available mutex_live mutex_access mutex_held mutex_ready mutex_owned : sl_opacity.
