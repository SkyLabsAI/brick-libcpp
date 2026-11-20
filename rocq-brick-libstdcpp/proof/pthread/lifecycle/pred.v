(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.lifecycle.model.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.iris.extra.bi.embedding.
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.bi.tls_modalities.
From iris.base_logic.lib Require Import ghost_map ghost_var.

Module lifecycle.
  Export lifecycle.

  Section resources.
    Context `{Σ : cpp_logic, !G _Σ}.

    (** Keep the process's designated registry authority in the library's
        synchronization protocol. Clients hold its ID leases and join rights. *)
    Local Definition registry_own_def (r : registry) (s : state) : mpred :=
      ⎡ ghost_map_auth (Σ := _Σ) r (DfracOwn 1) s ⎤%I.
    Local Definition registry_own_sealed : seal (@registry_own_def).
    Proof. by eexists. Qed.
    Definition registry_own := registry_own_sealed.(unseal).
    Local Definition registry_own_unseal : registry_own = @registry_own_def :=
      registry_own_sealed.(seal_eq).

    (** A temporary, fractionally shareable lease. Equalities on live IDs
        borrow this resource. Retiring a generation requires every fraction. *)
    Local Definition id_valid_def (r : registry) (q : Qp) (tid : thread_idT)
        (g : generation) : mpred :=
      ⎡ ghost_map_elem (Σ := _Σ) r (tid, false) (DfracOwn q) g ⎤%I.
    Local Definition id_valid_sealed : seal (@id_valid_def).
    Proof. by eexists. Qed.
    Definition id_valid := id_valid_sealed.(unseal).
    Local Definition id_valid_unseal : id_valid = @id_valid_def :=
      id_valid_sealed.(seal_eq).

    (** There is one full join right for a joinable ID in this registry. Its
        owner can change through synchronized transfer. *)
    Local Definition join_right_def (r : registry) (tid : thread_idT)
        (g : generation) : mpred :=
      ⎡ ghost_map_elem (Σ := _Σ) r (tid, true) (DfracOwn 1) g ⎤%I.
    Local Definition join_right_sealed : seal (@join_right_def).
    Proof. by eexists. Qed.
    Definition join_right := join_right_sealed.(unseal).
    Local Definition join_right_unseal : join_right = @join_right_def :=
      join_right_sealed.(seal_eq).

    (** The registry owner retains the epoch for a lease issued to an
        already executing thread. This token has no worker transition. *)
    Local Definition id_only_epoch_def (tid : thread_idT) (g : generation) : mpred :=
      ⎡ ghost_var (Σ := _Σ) g (DfracOwn 1) (tid, IdentityOnly) ⎤%I.
    Local Definition id_only_epoch_sealed : seal (@id_only_epoch_def).
    Proof. by eexists. Qed.
    Definition id_only_epoch := id_only_epoch_sealed.(unseal).
    Local Definition id_only_epoch_unseal : id_only_epoch = @id_only_epoch_def :=
      id_only_epoch_sealed.(seal_eq).

    Local Definition running_def (tid : thread_idT) (g : generation) : mpred :=
      ⎡ ghost_var (Σ := _Σ) g (DfracOwn 1) (tid, Running) ⎤%I.
    Local Definition running_sealed : seal (@running_def).
    Proof. by eexists. Qed.
    Definition running := running_sealed.(unseal).
    Local Definition running_unseal : running = @running_def :=
      running_sealed.(seal_eq).

    Local Definition terminated_def (tid : thread_idT) (g : generation)
        (result : ptr) : mpred :=
      ⎡ ghost_var (Σ := _Σ) g (DfracOwn 1) (tid, Complete result) ⎤%I.
    Local Definition terminated_sealed : seal (@terminated_def).
    Proof. by eexists. Qed.
    Definition terminated := terminated_sealed.(unseal).
    Local Definition terminated_unseal : terminated = @terminated_def :=
      terminated_sealed.(seal_eq).

    Local Definition joined_def (tid : thread_idT) (g : generation)
        (result : ptr) : mpred :=
      ⎡ ghost_var (Σ := _Σ) g (DfracOwn 1) (tid, Reaped result) ⎤%I.
    Local Definition joined_sealed : seal (@joined_def).
    Proof. by eexists. Qed.
    Definition joined := joined_sealed.(unseal).
    Local Definition joined_unseal : joined = @joined_def :=
      joined_sealed.(seal_eq).

    (** A synchronization contract must supply the transfer itself. These
        instances allow the same resources to be interpreted at the receiver
        when the two thread indices have the same process projection. *)
    #[global] Instance id_valid_local `{!HasStdThreads Σ} r q tid g :
      LocalWith procTI (id_valid r q tid g).
    Proof. rewrite id_valid_unseal /id_valid_def. apply embed_local_with. Qed.

    #[global] Instance join_right_local `{!HasStdThreads Σ} r tid g :
      LocalWith procTI (join_right r tid g).
    Proof. rewrite join_right_unseal /join_right_def. apply embed_local_with. Qed.

    #[global] Instance running_local `{!HasStdThreads Σ} tid g :
      LocalWith procTI (running tid g).
    Proof. rewrite running_unseal /running_def. apply embed_local_with. Qed.

    #[global] Instance terminated_local `{!HasStdThreads Σ} tid g result :
      LocalWith procTI (terminated tid g result).
    Proof. rewrite terminated_unseal /terminated_def. apply embed_local_with. Qed.

    Lemma join_right_exclusive r tid g1 g2 :
      join_right r tid g1 ** join_right r tid g2 |-- False.
    Proof.
      rewrite !join_right_unseal /join_right_def -embed_sep -(embed_pure False).
      apply embed_mono.
      iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne.
      contradiction.
    Qed.

    Lemma id_valid_split r tid g q1 q2 :
      id_valid r (q1 + q2)%Qp tid g -|-
      id_valid r q1 tid g ** id_valid r q2 tid g.
    Proof.
      rewrite !id_valid_unseal /id_valid_def -embed_sep.
      f_equiv.
      exact: (fractional
        (Φ := λ q, ghost_map_elem r (tid, false) (DfracOwn q) g) q1 q2).
    Qed.

    Lemma id_valid_agree r tid g1 g2 q1 q2 :
      id_valid r q1 tid g1 ** id_valid r q2 tid g2 |-- ⌜g1 = g2⌝%I.
    Proof.
      rewrite !id_valid_unseal /id_valid_def -embed_sep -(embed_pure (g1 = g2)).
      apply embed_mono.
      iIntros "[H1 H2]".
      iApply (ghost_map_elem_agree with "H1 H2").
    Qed.

    Lemma registry_alloc : |-- |==> Exists r, registry_own r ∅.
    Proof.
      rewrite /bi_emp_valid registry_own_unseal /registry_own_def -embed_exist -embed_bupd.
      rewrite -(embed_emp (PROP1 := iPropI _Σ)).
      apply embed_mono, ghost_map_alloc_empty.
    Qed.

    (** An already executing thread can acquire a lease for its own ID, for
        example for comparison with a newly created child. The designated
        registry owner establishes that this ID is absent. This bookkeeping
        step allocates neither a join right nor a worker start token. *)
    Lemma register_live_id `{!HasStdThreads Σ} r s tid :
      s !! (tid, false) = None ->
      s !! (tid, true) = None ->
      current_thread tid ** registry_own r s |-- |==> Exists g,
        current_thread tid **
        registry_own r (<[(tid, false) := g]> s) **
        id_valid r 1 tid g ** id_only_epoch tid g.
    Proof.
      intros Hid Hjoin.
      assert (Hstep : registry_own r s |-- |==> Exists g,
        registry_own r (<[(tid, false) := g]> s) **
        id_valid r 1 tid g ** id_only_epoch tid g).
      { rewrite registry_own_unseal /registry_own_def id_valid_unseal /id_valid_def
                id_only_epoch_unseal /id_only_epoch_def.
        repeat setoid_rewrite <- (embed_sep (PROP1 := iPropI _Σ)).
        rewrite -embed_exist -embed_bupd.
        apply embed_mono.
        iIntros "Hauth".
        iMod (ghost_var_alloc (tid, IdentityOnly)) as (g) "Hepoch".
        iMod (ghost_map_insert (tid, false) g with "Hauth") as "[Hauth Hid]"; first done.
        iModIntro. iExists g. iFrame. }
      iIntros "[Hthread Hauth]".
      iMod (Hstep with "Hauth") as (g) "(Hauth & Hid & Hepoch)".
      iModIntro. iExists g. iFrame.
    Qed.

    (** Return an ID-only lease after every borrower has finished. The owner
        can frame the epoch receipt. This bookkeeping change says nothing
        about physical thread exit. *)
    Lemma retire_live_id r s tid g :
      s !! (tid, true) = None ->
      registry_own r s ** id_valid r 1 tid g |-- |==>
      registry_own r (delete (tid, false) s).
    Proof.
      intros Hjoin.
      rewrite registry_own_unseal /registry_own_def id_valid_unseal /id_valid_def.
      rewrite -embed_sep -embed_bupd.
      apply embed_mono.
      iIntros "[Hauth Hid]".
      iApply (ghost_map_delete with "Hauth Hid").
    Qed.

    (** Use at the boundary of a successful creation. This is a ghost update for
        the newly created ID and supplies the worker's separate start token. *)
    Lemma register_joinable r s tid :
      s !! (tid, false) = None ->
      s !! (tid, true) = None ->
      registry_own r s |-- |==> Exists g,
        registry_own r (<[(tid, true) := g]> (<[(tid, false) := g]> s)) **
        id_valid r 1 tid g ** join_right r tid g ** running tid g.
    Proof.
      intros Hid Hjoin.
      rewrite registry_own_unseal /registry_own_def id_valid_unseal /id_valid_def
              join_right_unseal /join_right_def running_unseal /running_def.
      repeat setoid_rewrite <- (embed_sep (PROP1 := iPropI _Σ)).
      rewrite -embed_exist -embed_bupd.
      apply embed_mono.
      iIntros "Hauth".
      iMod (ghost_var_alloc (tid, Running)) as (g) "Hrunning".
      iMod (ghost_map_insert (tid, false) g with "Hauth") as "[Hauth Hid]"; first done.
      iMod (ghost_map_insert (tid, true) g with "Hauth") as "[Hauth Hjoin]".
      { by rewrite lookup_insert_ne. }
      iModIntro. iExists g. iFrame.
    Qed.

    (** Use at normal callback termination, with the actual callback pointer.
        The installed [current_thread] identifies the worker that can commit.
        This resource update entails no guarantee that a C callback returns. *)
    Lemma normal_return `{!HasStdThreads Σ} tid g result :
      current_thread tid ** running tid g
      |-- |==> current_thread tid ** terminated tid g result.
    Proof.
      assert (Hstep : running tid g |-- |==> terminated tid g result).
      { rewrite running_unseal /running_def terminated_unseal /terminated_def -embed_bupd.
        apply embed_mono.
        iIntros "Hrunning".
        iApply (ghost_var_update (tid, Complete result) with "Hrunning"). }
      iIntros "[Hthread Hrunning]".
      iMod (Hstep with "Hrunning") as "Hterminated".
      iModIntro. iFrame.
    Qed.

    (** Use at a successful join after receiving the worker's completion
        resource. The two fragments are consumed together, so the old lease
        and join right cannot survive reaping. The witness records the exact
        completed result for either result-pointer convention. *)
    Lemma join_reap r s tid g result :
      registry_own r s ** id_valid r 1 tid g ** join_right r tid g **
      terminated tid g result |-- |==>
        registry_own r (delete (tid, true) (delete (tid, false) s)) **
        joined tid g result.
    Proof.
      rewrite registry_own_unseal /registry_own_def id_valid_unseal /id_valid_def
              join_right_unseal /join_right_def terminated_unseal /terminated_def
              joined_unseal /joined_def.
      rewrite -!embed_sep -embed_bupd.
      apply embed_mono.
      iIntros "(Hauth & Hid & Hjoin & Hterminated)".
      iMod (ghost_map_delete with "Hauth Hid") as "Hauth".
      iMod (ghost_map_delete with "Hauth Hjoin") as "Hauth".
      iMod (ghost_var_update (tid, Reaped result) with "Hterminated") as "Hjoined".
      iModIntro. iFrame.
    Qed.
    (** A distinct joiner can use the transferred resources. The callable
        contract must establish the successful join and its non-cyclic use. *)
    Lemma join_reap_distinct `{!HasStdThreads Σ} r s joiner target g result :
      joiner <> target ->
      current_thread joiner **
        (registry_own r s ** id_valid r 1 target g ** join_right r target g **
          terminated target g result) |-- |==>
      current_thread joiner **
        registry_own r (delete (target, true) (delete (target, false) s)) **
        joined target g result.
    Proof.
      intros Hdistinct.
      iIntros "[Hthread Hready]".
      iMod (join_reap r s target g result with "Hready") as "[Hauth Hjoined]".
      iModIntro. iFrame.
    Qed.

  End resources.

End lifecycle.
