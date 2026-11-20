(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * SPDX-License-Identifier: BSD-3-Clause
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.mutex.spec.base_mutex.

Import linearity.

(** * Owner-tracking mutex invariant

    Ghost state and invariant shared by mutexes whose physical state is a
    single "held" bit, independently of how that bit is represented. Include
    this module in a [BASE_MUTEX_PREDS] instance, then define its [R] as
    [mutexR] of the type's own representation:
    - [tyR q] is the fractional ownership of the object itself, outside the
      invariant (e.g. [type_ptrR] or [structR]);
    - [phys this b] is the physical state of the mutex at [this], held iff [b].

    While the mutex is free, the invariant holds the guarded resource [P].
    The owner deposits its [not_locked] handle there and keeps the [locked]
    fragment recording its thread and share. *)
Module OwnerTidMutex.
  Record mutex_gname : Set := MkGname {
    token_gname : iprop.gname;
    owner_gname : iprop.gname;
    inv_gname : iprop.gname;
    inv_namespace : namespace;
    inv_namespace_not_root : inv_namespace <> nroot;
  }.
  Definition gname : Set := mutex_gname.
  Definition mutex_inv_namespace (g : gname) : namespace := g.(inv_namespace).
  Lemma mutex_inv_namespace_not_root g : mutex_inv_namespace g <> nroot.
  Proof. exact g.(inv_namespace_not_root). Qed.

  Class mutexG `{Σ : cpp_logic} := {
    #[global] tokens_G :: MutexTokens.G Σ;
    #[global] owners_G :: OwnerTid.G Σ;
  }.
  Definition G := @mutexG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance mutex_G `{Σ : cpp_logic} (H : G Σ) : @mutexG _ _ Σ := H.

  Definition token `{Σ : cpp_logic, !G Σ} (g : gname) (q : cQp.t) : mpred :=
    MutexTokens.token g.(token_gname) (cQp.frac q).
  #[global] Instance token_fractional `{Σ : cpp_logic, !G Σ} g :
      CFractional (token g).
  Proof. intros q1 q2. rewrite /token cQp.frac_add. apply MutexTokens.token_fractional. Qed.
  #[global] Instance token_timeless `{Σ : cpp_logic, !G Σ} g q :
      Timeless (token g q).
  Proof. rewrite /token. apply _. Qed.

  (** As in [BASE_MUTEX_PREDS]. *)
  Definition not_locked `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    token g qt ** MutexSets.my_mutexes th
      (coPset.CoPset $ ↑mutex_inv_namespace g).

  #[global] Instance not_locked_timeless
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g th qt :
    Timeless (not_locked this g th qt).
  Proof. rewrite /not_locked. apply _. Qed.
  #[global] Instance not_locked_exclusive
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g th :
    Exclusive1 (not_locked this g th).
  Proof.
    intros q1 q2. rewrite /not_locked. iIntros "[_ H1] [_ H2]".
    have Hoverlap : ~ ((↑mutex_inv_namespace g : coPset) ## ↑mutex_inv_namespace g).
    { have Hnonempty := nclose_non_empty (mutex_inv_namespace g). set_solver. }
    iDestruct (MutexSets.my_mutexes_exclusive _ _ _ Hoverlap with "[$H1 $H2]") as %[].
  Qed.

  Definition locked `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (_this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    OwnerTid.owner_tid_frag g.(owner_gname) (Some (th, qt)).

  (** Learn the share [qt] from the mutex, its ghost name and the thread. *)
  #[global] Instance not_locked_learn
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g th :
    LearnEq1 (not_locked this g th).
  Proof. solve_learnable. Qed.
  #[global] Instance locked_learn_share
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g th :
    LearnEq1 (locked this g th).
  Proof. solve_learnable. Qed.

  #[global] Instance locked_timeless
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g th qt :
    Timeless (locked this g th qt).
  Proof. rewrite /locked. apply _. Qed.
  #[global] Instance locked_exclusive
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g :
    Exclusive2 (locked this g).
  Proof. intros th1 th2 qt1 qt2. rewrite /locked. apply _. Qed.
  #[global] Instance locked_WeaklyObjective
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this g th qt :
    WeaklyObjective (locked this g th qt).
  Proof. rewrite /locked. apply _. Qed.

  (** The invariant: the physical bit agrees with the ghost owner. *)
  Definition state `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (phys : ptr -> bool -> mpred) (this : ptr) (g : gname) (P : mpred) : mpred :=
    ∃ owner : option (thread_idT * cQp.t),
      phys this (bool_decide (is_Some owner)) **
      OwnerTid.owner_tid_auth g.(owner_gname) owner **
      match owner with
      | None => OwnerTid.owner_tid_frag g.(owner_gname) None ** P
      | Some (th, qt) => not_locked this g th qt
      end.

  #[global] Instance state_WeaklyObjective
      `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ} phys this g P :
    (forall b, WeaklyObjective (phys this b)) ->
    WeaklyObjective P -> WeaklyObjective (state phys this g P).
  Proof.
    intros. rewrite /state /not_locked /token /MutexTokens.token.
    apply _.
  Qed.

  Definition mutexR `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (tyR : cQp.t -> Rep) (phys : ptr -> bool -> mpred)
      (g : gname) (q : cQp.t) (P : mpred) : Rep :=
    tyR q **
    as_Rep (fun this => cinv (mutex_inv_namespace g) g.(inv_gname) (state phys this g P)) **
    pureR (cinv_own g.(inv_gname) q).

  #[global] Instance locked_learn
      `{Σ : cpp_logic} `{MUTEX_SETS : !mutex_set_G Σ} `{!G Σ} {σ : genv} :
    Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> req_eq ==> learn_hints.fin) locked).
  Proof. solve_learnable. Qed.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}.
    Context (tyR : cQp.t -> Rep) (phys : ptr -> bool -> mpred).
    #[local] Existing Instance mpred_BiAffine.

    (** Set up a fresh mutex from its free physical state. *)
    Lemma mutexR_alloc (this : ptr) (N : namespace) (P : mpred) :
      (forall b, WeaklyObjective (phys this b)) ->
      WeaklyObjective P ->
      N <> nroot ->
      this |-> tyR 1$m ** ▷ phys this false ** ▷P |--
        (|={⊤}=> ∃ g, [| mutex_inv_namespace g = N |] **
          this |-> mutexR tyR phys g 1$m P ** token g 1$m).
    Proof.
      intros Hphys HP HN. iIntros "(Ty & Raw & P)".
      iMod MutexTokens.alloc as (gt) "Tnew".
      iMod (OwnerTid.alloc None) as (go) "[OA OF]".
      iMod (cinv_alloc_cofinite ∅ ⊤ N) as (gi) "(_ & COnew & Alloc)".
      iMod ("Alloc" $! (state phys this (MkGname gt go gi N HN) P)
        with "[] [Raw OA OF P]") as "#CInew".
      { iPureIntro. apply _. }
      { iNext. rewrite /state. iExists None. iFrame. }
      iModIntro. iExists (MkGname gt go gi N HN).
      iSplit; first (iPureIntro; reflexivity).
      rewrite /mutexR /token !_at_sep !_at_pureR !_at_as_Rep /=.
      iFrame "Ty CInew". iFrame.
    Qed.

    (** Retire a mutex. The full lifetime token excludes an owner, and the full
        share of [mutexR] excludes pending calls. *)
    Lemma mutexR_cancel (this : ptr) g P :
      this |-> mutexR tyR phys g 1$m P ** token g 1$m |--
        (|={⊤}=> this |-> tyR 1$m ** ▷ phys this false ** ▷P).
    Proof.
      iIntros "(HR & T)".
      rewrite /mutexR !_at_sep !_at_pureR !_at_as_Rep.
      iDestruct "HR" as "(Ty & #CI & CO)".
      iMod (cinv_cancel with "CI CO") as "St"; first done.
      iDestruct "St" as (owner) "(Raw & >Auth & Rest)".
      destruct owner as [[th qt]|].
      - iDestruct "Rest" as ">Rest". rewrite /not_locked /token.
        iDestruct "Rest" as "[Held _]".
        iDestruct (MutexTokens.token_valid_2 with "[$T $Held]") as %Hbad.
        exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt) Hbad).
      - iDestruct "Rest" as "[_ P]". iModIntro. iFrame.
    Qed.

    Lemma mutexR_cancel_timeless (this : ptr) g P :
      (forall b, Timeless (phys this b)) ->
      this |-> mutexR tyR phys g 1$m P ** token g 1$m |--
        (|={⊤}=> this |-> tyR 1$m ** phys this false ** ▷P).
    Proof.
      intros Ht. iIntros "H".
      iMod (mutexR_cancel with "H") as "($ & >$ & $)". done.
    Qed.

    Lemma mutexR_reinit (this : ptr) (old : gname) (N : namespace) (P : mpred) :
      (forall b, WeaklyObjective (phys this b)) ->
      WeaklyObjective P ->
      N <> nroot ->
      this |-> mutexR tyR phys old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g,
          [| mutex_inv_namespace g = N |] **
          this |-> mutexR tyR phys g 1$m P ** token g 1$m).
    Proof.
      intros Hphys HP HN. iIntros "(HR & T & P)".
      iMod (mutexR_cancel with "[$HR $T]") as "(Ty & Raw & _)".
      iApply (mutexR_alloc with "[$Ty $Raw $P]"); done.
    Qed.

    Lemma mutexR_locked_my_mutexes_exclusive (this : ptr) g th q qt P E :
      ↑mutex_inv_namespace g ⊆ E ->
      this |-> mutexR tyR phys g q P ** locked this g th qt **
        MutexSets.my_mutexes th
          (coPset.CoPset $ ↑mutex_inv_namespace g) |-- (|={E}=> False).
    Proof.
      intros Hmask. rewrite /mutexR /locked !_at_sep !_at_pureR !_at_as_Rep.
      iIntros "((_ & #HI & HO) & HF & Hnames)".
      iInv "HI" as "[(%owner & _ & >HA & HS) HO]".
      iDestruct (observe_2 [|owner = Some (th, qt)|] with "HA HF") as %->.
      iDestruct "HS" as ">HS". rewrite /not_locked.
      iDestruct "HS" as "[_ Hheld]".
      iDestruct (MutexSets.my_mutexes_exclusive with "[$Hheld $Hnames]") as %[].
      have Hnonempty := nclose_non_empty (mutex_inv_namespace g). set_solver.
    Qed.

    (** A full lifetime token excludes an owner, which has deposited a positive
        share. *)
    Lemma mutexR_locked_full_token (this : ptr) g q P th qt :
      this |-> mutexR tyR phys g q P ** token g 1$m ** locked this g th qt |--
        (|={⊤}=> False).
    Proof.
      rewrite /mutexR /locked !_at_sep !_at_pureR !_at_as_Rep.
      iIntros "((_ & #HI & HO) & HT & HF)".
      iInv "HI" as "[(%owner & _ & >HA & HS) HO]".
      iDestruct (observe_2 [|owner = Some (th, qt)|] with "HA HF") as %->.
      iDestruct "HS" as ">HS". rewrite /not_locked /token.
      iDestruct "HS" as "[Held _]".
      iDestruct (MutexTokens.token_valid_2 with "[$HT $Held]") as %Hbad.
      exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt) Hbad).
    Qed.

    (** ** Ghost steps for implementation proofs, inside the invariant *)

    (** Acquiring a free mutex: deposit [not_locked], take [locked] and [P]. *)
    Lemma state_acquire this g th qt :
      OwnerTid.owner_tid_auth g.(owner_gname) None **
      OwnerTid.owner_tid_frag g.(owner_gname) None **
      not_locked this g th qt |--
        |==> OwnerTid.owner_tid_auth g.(owner_gname) (Some (th, qt)) **
          not_locked this g th qt ** locked this g th qt.
    Proof.
      iIntros "(A & F & NL)". rewrite /locked.
      iMod (OwnerTid.owner_update _ _ _ (Some (th, qt)) with "[$A $F]") as "[$ $]".
      by iFrame.
    Qed.

    (** Releasing: return [locked], take back [not_locked]. *)
    Lemma state_release this g th qt owner :
      OwnerTid.owner_tid_auth g.(owner_gname) owner ** locked this g th qt |--
        |==> [| owner = Some (th, qt) |] **
          OwnerTid.owner_tid_auth g.(owner_gname) None **
          OwnerTid.owner_tid_frag g.(owner_gname) None.
    Proof.
      rewrite /locked. iIntros "[A F]".
      iDestruct (observe_2 [| owner = Some (th, qt) |] with "A F") as %->.
      iMod (OwnerTid.owner_update _ _ _ None with "[$A $F]") as "[$ $]".
      done.
    Qed.

    (** The owner's [locked] fragment determines the ghost owner. *)
    Lemma state_owner this g th qt owner :
      OwnerTid.owner_tid_auth g.(owner_gname) owner ** locked this g th qt |--
        [| owner = Some (th, qt) |].
    Proof.
      rewrite /locked. iIntros "[A F]".
      iDestruct (observe_2 [| owner = Some (th, qt) |] with "A F") as %->. done.
    Qed.

    (** A full share of the lifetime token excludes any owner. *)
    Lemma state_full_token this g th owner :
      OwnerTid.owner_tid_auth g.(owner_gname) owner **
      (match owner with
       | None => emp
       | Some (th', qt') => not_locked this g th' qt'
       end) ** not_locked this g th 1$m |-- [| owner = None |].
    Proof.
      destruct owner as [[th' qt']|]; last by iIntros "_".
      rewrite /not_locked /token. iIntros "(_ & [Held _] & [T _])".
      iDestruct (MutexTokens.token_valid_2 with "[$T $Held]") as %Hbad.
      exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt') Hbad).
    Qed.
  End with_cpp.

  #[global] Hint Opaque token not_locked locked state mutexR : sl_opacity typeclass_instances.
End OwnerTidMutex.
