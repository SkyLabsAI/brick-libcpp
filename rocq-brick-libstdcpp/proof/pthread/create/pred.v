(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.create.model.
Require Export skylabs.brick.libstdcpp.pthread.lifecycle.spec.
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.iris.extra.bi.embedding.
Require Import skylabs.iris.extra.bi.invariants.
Require Import skylabs.iris.extra.base_logic.monpred_invariants.
Require Import skylabs.iris.extra.proofmode.proofmode.

Module pthread_create.
  Export pthread_create.

  Section resources.
    Context `{Σ : cpp_logic, !HasStdThreads Σ, !lifecycle.G _Σ}.

    Local Lemma proc_le (i j : thread_info) : i ⊑ j -> i .^ procTI = j .^ procTI.
    Proof. exact: (mlens_get_mono procTI i j). Qed.

    Local Lemma process_local_weaken (P : mpred) :
      LocalWith procTI P -> WeaklyObjective P.
    Proof. intros Hlocal i j Hle. apply Hlocal. symmetry. exact: proc_le. Qed.

    Local Lemma inv_process_local N (P : mpred) :
      LocalWith procTI P -> LocalWith procTI (inv N P).
    Proof.
      intros Hlocal. rewrite inv_eq /inv_def. apply _.
    Qed.

    (** Process bootstrap supplies this persistent assertion for the single
        registry selected by the process's [ProcessRegistry] context. The
        external library alone accesses its authority at synchronization
        boundaries. Clients hold only the assertion and their fragments. *)
    Local Definition registry_sync_def (r : lifecycle.registry) : mpred :=
      inv registry_namespace (∃ s, lifecycle.registry_own r s)%I.
    Local Definition registry_sync_sealed : seal registry_sync_def.
    Proof. by eexists. Qed.
    Definition registry_sync := registry_sync_sealed.(unseal).
    Local Definition registry_sync_unseal : registry_sync = registry_sync_def :=
      registry_sync_sealed.(seal_eq).

    #[global] Instance registry_sync_persistent r : Persistent (registry_sync r).
    Proof. rewrite registry_sync_unseal /registry_sync_def. apply _. Qed.

    (** The library opens this invariant at the synchronized commit or reap
        boundary. The guarded authority requires a program step before use. *)
    Local Lemma registry_access E r :
      ↑registry_namespace ⊆ E ->
      registry_sync r ⊢ |={E,E∖↑registry_namespace}=>
        ▷ (∃ s, lifecycle.registry_own r s) ∗
        (▷ (∃ s, lifecycle.registry_own r s) ={E∖↑registry_namespace,E}=∗ emp).
    Proof.
      intros Hmask. rewrite registry_sync_unseal /registry_sync_def.
      iIntros "Hinv". iApply (inv_acc with "Hinv"). exact Hmask.
    Qed.

    (** The escrow's phase uses its own ghost name. Pending owns half the
        running marker and the worker owns the other half. The full marker
        moves to completed and then claimed. The escrow's [Reaped] tag records
        collection, while [lifecycle.joined] records registry reaping. *)
    Local Definition marker (key : gname) (tid : thread_idT) (q : Qp)
        (phase : lifecycle.phase) : mpred :=
      ⎡ ghost_var (Σ := _Σ) key (DfracOwn q) (tid, phase) ⎤%I.

    #[local] Instance marker_timeless key tid q phase : Timeless (marker key tid q phase).
    Proof. rewrite /marker. apply _. Qed.

    Definition completed (tid : thread_idT) (g : lifecycle.generation)
        (Post : ptr -> mpred) : mpred :=
      (∃ result, lifecycle.terminated tid g result ∗ Post result)%I.

    Local Definition escrow_body key tid g Post : mpred :=
      (marker key tid (1/2) lifecycle.Running ∨
       (∃ result, marker key tid 1 (lifecycle.Complete result) ∗
          lifecycle.terminated tid g result ∗ Post result) ∨
       (∃ result, marker key tid 1 (lifecycle.Reaped result)))%I.

    Local Definition escrow key tid g Post : mpred :=
      inv completion_namespace (escrow_body key tid g Post).

    (** A caller receives the unique right to claim from this exact escrow.
        The right can be passed by synchronized process-local transfer even
        while the worker is running. *)
    Local Definition completion_right_def r tid g Post : mpred :=
      (lifecycle.join_right r tid g ∗ ∃ key, escrow key tid g Post)%I.
    Local Definition completion_right_sealed : seal completion_right_def.
    Proof. by eexists. Qed.
    Definition completion_right := completion_right_sealed.(unseal).
    Local Definition completion_right_unseal : completion_right = completion_right_def :=
      completion_right_sealed.(seal_eq).

    (** The library retains the publication part for the worker. The actual
        callback receives [running] and returns it alongside [Post result]. *)
    Local Definition worker_publication_def tid g Post : mpred :=
      (∃ key, marker key tid (1/2) lifecycle.Running ∗ escrow key tid g Post)%I.
    Local Definition worker_publication_sealed : seal worker_publication_def.
    Proof. by eexists. Qed.
    Definition worker_publication := worker_publication_sealed.(unseal).
    Local Definition worker_publication_unseal : worker_publication = worker_publication_def :=
      worker_publication_sealed.(seal_eq).

    #[local] Instance escrow_body_local key tid g Post
        `{!∀ result, LocalWith procTI (Post result)} :
      LocalWith procTI (escrow_body key tid g Post).
    Proof. rewrite /escrow_body /marker. apply _. Qed.

    #[local] Instance escrow_local key tid g Post
        `{!∀ result, LocalWith procTI (Post result)} :
      LocalWith procTI (escrow key tid g Post).
    Proof. rewrite /escrow. apply inv_process_local, _. Qed.

    #[global] Instance completion_right_local r tid g Post
        `{!∀ result, LocalWith procTI (Post result)} :
      LocalWith procTI (completion_right r tid g Post).
    Proof.
      rewrite completion_right_unseal /completion_right_def. apply _.
    Qed.

    #[global] Instance worker_publication_local tid g Post
        `{!∀ result, LocalWith procTI (Post result)} :
      LocalWith procTI (worker_publication tid g Post).
    Proof. rewrite worker_publication_unseal /worker_publication_def. apply _. Qed.

    Lemma completion_right_exclusive r tid g1 g2 Post1 Post2 :
      completion_right r tid g1 Post1 ∗ completion_right r tid g2 Post2 ⊢ False.
    Proof.
      rewrite !completion_right_unseal /completion_right_def.
      iIntros "[[H1 _] [H2 _]]".
      iApply (lifecycle.join_right_exclusive with "[$H1 $H2]").
    Qed.

    Local Lemma marker_alloc tid : ⊢ |==> ∃ key, marker key tid 1 lifecycle.Running.
    Proof.
      rewrite /bi_emp_valid /marker -embed_exist -embed_bupd.
      rewrite -(embed_emp (PROP1 := iPropI _Σ)).
      apply embed_mono, ghost_var_alloc.
    Qed.

    Local Lemma marker_split key tid phase :
      marker key tid 1 phase ⊣⊢ marker key tid (1/2) phase ∗ marker key tid (1/2) phase.
    Proof.
      rewrite /marker -embed_sep. f_equiv.
      rewrite -{1}Qp.half_half.
      exact: (fractional
        (Φ := λ q, ghost_var key (DfracOwn q) (tid, phase)) (1/2)%Qp (1/2)%Qp).
    Qed.

    Local Lemma marker_agree key tid q1 q2 phase1 phase2 :
      marker key tid q1 phase1 ∗ marker key tid q2 phase2 ⊢ ⌜phase1 = phase2⌝.
    Proof.
      rewrite /marker -embed_sep -(embed_pure (phase1 = phase2)).
      apply embed_mono.
      iIntros "[H1 H2]".
      iDestruct (ghost_var_valid_2 with "H1 H2") as %[_ Hagree].
      iPureIntro. by injection Hagree.
    Qed.

    Local Lemma marker_update key tid phase1 phase2 :
      marker key tid 1 phase1 ⊢ |==> marker key tid 1 phase2.
    Proof.
      rewrite /marker -embed_bupd. apply embed_mono.
      iIntros "Hphase". iApply (ghost_var_update (tid, phase2) with "Hphase").
    Qed.

    (** The successful commit consumes transient access to the synchronized
        registry and returns its updated authority before the worker starts. *)
    Lemma register_success E r s tid Post
        `{!∀ result, LocalWith procTI (Post result)} :
      s !! (tid, false) = None -> s !! (tid, true) = None ->
      lifecycle.registry_own r s ⊢ |={E}=> ∃ g,
        lifecycle.registry_own r (<[(tid, true) := g]> (<[(tid, false) := g]> s)) ∗
        lifecycle.id_valid r 1 tid g ∗ completion_right r tid g Post ∗
        lifecycle.running tid g ∗ worker_publication tid g Post.
    Proof.
      intros Hid Hjoin.
      iIntros "Hauth".
      iMod (lifecycle.register_joinable _ _ _ Hid Hjoin with "Hauth")
        as (g) "(Hauth & Hid & Hright & Hrunning)".
      iMod (marker_alloc tid) as (key) "Hkey".
      iDestruct (marker_split with "Hkey") as "[Hpending Hkey]".
      have Hwo : WeaklyObjective (escrow_body key tid g Post).
      { apply process_local_weaken, _. }
      iMod (monpred_invariants.inv_alloc completion_namespace E (escrow_body key tid g Post)
              with "[Hpending]") as "#Hescrow".
      { iNext. iLeft. iExact "Hpending". }
      iModIntro. iExists g.
      rewrite completion_right_unseal worker_publication_unseal
        /completion_right_def /worker_publication_def.
      iFrame "Hauth Hid".
      iSplitL "Hright".
      - iFrame "Hright". iExists key. iExact "Hescrow".
      - iFrame "Hrunning". iExists key. iFrame "Hkey Hescrow".
    Qed.

    (** Only the worker that owns the publication token may make a completed
        result available. The library performs this update at normal return. *)
    Lemma publish_return E tid g Post result :
      ↑completion_namespace ⊆ E ->
      current_thread tid ∗ lifecycle.running tid g ∗ worker_publication tid g Post ∗
        Post result ⊢ |={E}=> current_thread tid.
    Proof.
      intros Hmask.
      rewrite worker_publication_unseal /worker_publication_def /escrow.
      iIntros "(Hthread & Hrunning & Hworker & Hpost)".
      iDestruct "Hworker" as (key) "[Hkey #Hescrow]".
      iMod (lifecycle.normal_return _ _ result with "[$Hthread $Hrunning]")
        as "[Hthread Hterminated]".
      iMod (inv_acc with "Hescrow") as "[Hstate Hclose]"; first exact Hmask.
      rewrite /escrow_body.
      iDestruct "Hstate" as "[Hpending | [Hready | Hreaped]]".
      - iMod "Hpending" as "Hpending".
        iAssert (marker key tid 1 lifecycle.Running) with "[Hkey Hpending]" as "Hfull".
        { rewrite marker_split. iFrame. }
        iMod (marker_update _ _ _ (lifecycle.Complete result) with "Hfull") as "Hfull".
        iMod ("Hclose" with "[Hfull Hterminated Hpost]"); last by iFrame.
        iNext. iRight. iLeft. iExists result. iFrame.
      - iDestruct "Hready" as (previous) "Hready".
        iEval (rewrite bi.later_sep) in "Hready".
        iDestruct "Hready" as "[Hother Hpayload]".
        iMod "Hother" as "Hother".
        iDestruct (marker_agree with "[$Hkey $Hother]") as %Hbad.
        discriminate.
      - iDestruct "Hreaped" as (previous) "Hother".
        iMod "Hother" as "Hother".
        iDestruct (marker_agree with "[$Hkey $Hother]") as %Hbad.
        discriminate.
    Qed.

    (** A join implementation can check the escrow. The pending branch gives
        the same right back. The completed branch marks the escrow claimed and
        preserves the registry join fragment for reaping. The later modality
        is discharged by a program step in the synchronized operation. *)
    Lemma claim_completion E r tid g Post :
      ↑completion_namespace ⊆ E ->
      completion_right r tid g Post ⊢ |={E}=>
        completion_right r tid g Post ∨
        (lifecycle.join_right r tid g ∗ ▷ completed tid g Post).
    Proof.
      intros Hmask.
      rewrite completion_right_unseal /completion_right_def /escrow.
      iIntros "[Hright Hescrow]".
      iDestruct "Hescrow" as (key) "#Hescrow".
      iMod (inv_acc with "Hescrow") as "[Hstate Hclose]"; first exact Hmask.
      rewrite /escrow_body.
      iDestruct "Hstate" as "[Hpending | [Hready | Hreaped]]".
      - iMod ("Hclose" with "[Hpending]") as "_"; first by iNext; iLeft.
        iModIntro. iLeft. iFrame "Hright". iExists key. iExact "Hescrow".
      - iDestruct "Hready" as (result) "Hready".
        iEval (rewrite bi.later_sep) in "Hready".
        iDestruct "Hready" as "[Hmarker Hcompleted]".
        iMod "Hmarker" as "Hmarker".
        iMod (marker_update _ _ _ (lifecycle.Reaped result) with "Hmarker") as "Hmarker".
        iMod ("Hclose" with "[Hmarker]") as "_".
        { iNext. iRight. iRight. iExists result. iExact "Hmarker". }
        iModIntro. iRight. iFrame "Hright".
        iNext. iExists result. iExact "Hcompleted".
      - iMod ("Hclose" with "[Hreaped]") as "_"; first by iNext; iRight; iRight.
        iModIntro. iLeft. iFrame "Hright". iExists key. iExact "Hescrow".
    Qed.

    Lemma reap_completed r s tid g (Post : ptr -> mpred) :
      lifecycle.registry_own r s ∗ lifecycle.id_valid r 1 tid g ∗
        lifecycle.join_right r tid g ∗ completed tid g Post ⊢ |==> ∃ result,
        lifecycle.registry_own r (delete (tid, true) (delete (tid, false) s)) ∗
        lifecycle.joined tid g result ∗ Post result.
    Proof.
      iIntros "(Hauth & Hid & Hright & Hcompleted)".
      iDestruct "Hcompleted" as (result) "[Hterminated Hpost]".
      iMod (lifecycle.join_reap _ _ _ _ _ with "[$Hauth $Hid $Hright $Hterminated]")
        as "[Hauth Hjoined]".
      iModIntro. iExists result. iFrame.
    Qed.
  End resources.
End pthread_create.
