(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * SPDX-License-Identifier: BSD-3-Clause
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.zeroR.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Export skylabs.brick.libstdcpp.mutex.spec.base_mutex.

Import linearity.
Export lock_ghost2.mutex_set_G (mutex_set_G).

Module pthread_errno.
  (** EBUSY is 16 in the Linux ABI used by this library's toolchain. *)
  Definition EBUSY : Z := 16.
End pthread_errno.

(** * Contracts of pthread-style mutex functions

    The calling convention of Linux/glibc's default pthread mutex, over any
    [BASE_MUTEX_PREDS]: functions take the mutex by pointer and return an [int]
    status. The ordinary lifecycle and acquisition contracts reuse the bodies of
    [base_mutex_spec], which the C++ mutex specs share. The remaining contracts
    are specific to the default (NORMAL) pthread mutex type.

    [pthread.mutex] below instantiates these contracts for glibc's mutex as
    trusted library specifications; test/pthread/custom_mutex.hpp proves them
    for a spinlock implementation. *)
Module pthread_mutex_spec (Preds : BASE_MUTEX_PREDS).
  Include base_mutex_spec Preds.

Section with_cpp.
  Import Preds.
  Import pthread_errno.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!G Σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  (** Only default initialization (a null attribute pointer) is described.
      Ownership of the entire storage excludes initialization of a live mutex
      and any concurrent access. *)
  Definition init_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \pre this |-> anyR cpp_ty 1$m
    \arg "mutexattr" (Vptr nullptr)
    \exact Reduce (ctor_body (Vint 0) this).

  (** Unlike a C++ destructor, [destroy] returns the raw storage explicitly. *)
  Definition destroy_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \pre{g P} this |-> R g 1$m P ** token g 1$m
    \post[Vint 0] this |-> anyR cpp_ty 1$m ** P.

  Definition lock_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \exact Reduce (lock_body (Vint 0) this).

  Definition unlock_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \exact Reduce (unlock_body (Vint 0) this).

  Definition trylock_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \exact Beta (Reduce
      (try_lock_body (fun success => Vint (if success then 0 else EBUSY)) this)).

  (** ** Contracts specific to the default (NORMAL) mutex type *)

  (** Relocking by its owner blocks forever: a defined non-return under partial
      correctness, not undefined behavior. P can be framed; it is not consumed
      by relocking. *)
  Definition lock_owned_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \prepost{g q P} this |-> R g q P
    \persist{th} current_thread th
    \pre{qt} locked this g th qt
    \post{ret : Z}[Vint ret] False.

  (** trylock returns EBUSY, including for its owner. *)
  Definition trylock_owned_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \prepost{g q P} this |-> R g q P
    \persist{th} current_thread th
    \prepost{qt} locked this g th qt
    \post[Vint EBUSY] emp.

  (** A held token may be temporarily handed to another thread for this
      observation. The owner cannot unlock concurrently without that token,
      so trylock definitely returns EBUSY, whichever thread calls it. No
      acquisition permission is needed and no ownership is granted. *)
  Definition trylock_held_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \prepost{g q P} this |-> R g q P
    \prepost{owner qt} locked this g owner qt
    \post[Vint EBUSY] emp.

  (** Full R excludes another active call, and the full lifetime token
      contained in not_locked excludes any owner. Thus acquisition really
      succeeds, rather than exhibiting std::mutex's spurious failure. In
      the shared rule, EBUSY does not imply the mutex is still held at
      return: an interfering owner may already have released it. *)
  Definition trylock_uncontended_spec : WpSpec mpred val val :=
    \arg{this} "mutex" (Vptr this)
    \prepost{g P} this |-> R g 1$m P
    \persist{th} current_thread th
    \pre not_locked this g th 1$m
    \post[Vint 0] locked this g th 1$m ** P.
End with_cpp.
End pthread_mutex_spec.

Module pthread.
Export skylabs.brick.libstdcpp.pthread.pred.pthread.

(** Linux/glibc's default mutex: NORMAL, process-private, non-robust,
    PTHREAD_PRIO_NONE. These are trusted library specifications, not proofs
    of glibc's implementation. No recursive, robust, process-shared, or
    priority-protection attribute is covered by this representation.

    In particular, glibc maps DEFAULT to NORMAL. Relocking by its owner
    blocks forever; trylock instead returns EBUSY, including for its owner.
    An exclusive, uncontended trylock rule below excludes spurious failure. *)
Module MutexPreds <: BASE_MUTEX_PREDS.
  Definition cpp_ty : type := "pthread_mutex_t".

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

  (** Exclusive physical ownership of the default pthread mutex. Its boolean
      records whether it is held. Its bytes are hidden behind the invariant:
      clients cannot inspect or copy an initialized mutex. Like the physical
      points-to of [runtime.objective], it is local to its process, hence weakly
      objective. *)
  Parameter rawR : forall `{Σ : cpp_logic, σ : genv}, bool -> Rep.
  Axiom rawR_local : forall `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ} b,
    LocalWithR procTI (rawR b).
  #[global] Existing Instance rawR_local.
  #[global] Instance rawR_weakly_objective `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}
      (this : ptr) b :
    WeaklyObjective (this |-> rawR b).
  Proof. apply LocalWith_procTI_weakly_objective, _. Qed.

  Definition state `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (this : ptr) (g : gname) (P : mpred) : mpred :=
    ∃ owner : option (thread_idT * cQp.t),
      this |-> rawR (bool_decide (is_Some owner)) **
      OwnerTid.owner_tid_auth g.(owner_gname) owner **
      match owner with
      | None => OwnerTid.owner_tid_frag g.(owner_gname) None ** P
      | Some (th, qt) => not_locked this g th qt
      end.

  #[global] Instance state_WeaklyObjective
      `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ} this g P :
    WeaklyObjective P -> WeaklyObjective (state this g P).
  Proof.
    intros. rewrite /state /not_locked /token /MutexTokens.token.
    apply _.
  Qed.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.
    #[local] Existing Instance mpred_BiAffine.

    Definition R {HAS_THREADS : HasStdThreads Σ} {σ : genv}
        (g : gname) (q : cQp.t) (P : mpred) : Rep :=
      type_ptrR "pthread_mutex_t" **
      as_Rep (fun this => cinv (mutex_inv_namespace g) g.(inv_gname) (state this g P)) **
      pureR (cinv_own g.(inv_gname) q).
    #[global] Hint Opaque R : sl_opacity typeclass_instances.
    #[only(cfractional,cfracvalid,ascfractional)] derive R.

    #[global] Instance R_type_ptr {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P :
      Observe (type_ptrR cpp_ty) (R g q P).
    Proof. rewrite /R /cpp_ty. apply _. Qed.
    #[global] Instance R_learnable {HAS_THREADS : HasStdThreads Σ} {σ : genv} :
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    Context {σ : genv}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    #[global] Instance locked_learn :
        Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> req_eq ==> learn_hints.fin) locked).
    Proof using MUTEX_SETS. solve_learnable. Qed.

    Lemma init_R (this : ptr) (old : gname) (N : namespace) (P : mpred) :
      WeaklyObjective P ->
      N <> nroot ->
      this |-> R old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g,
          [| mutex_inv_namespace g = N |] **
          this |-> R g 1$m P ** token g 1$m).
    Proof.
      intros HP HN. iIntros "(HR & T & P)".
      rewrite /R !_at_sep !_at_pureR !_at_as_Rep.
      iDestruct "HR" as "(Ty & #CI & CO)".
      iMod (cinv_cancel with "CI CO") as "St"; first done.
      iDestruct "St" as (owner) "(Raw & >Auth & Rest)".
      destruct owner as [[th qt]|].
      - iDestruct "Rest" as ">Rest". rewrite /not_locked /token.
        iDestruct "Rest" as "[Held Hmine]".
        iDestruct (MutexTokens.token_valid_2 with "[$T $Held]") as %Hbad.
        exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt) Hbad).
      - iDestruct "Rest" as "[>Frag _]".
        iMod MutexTokens.alloc as (gt) "Tnew".
        iMod (OwnerTid.alloc None) as (go) "[OA OF]".
        iMod (cinv_alloc_cofinite ∅ ⊤ N) as (gi) "(_ & COnew & Alloc)".
        iMod ("Alloc" $! (state this (MkGname gt go gi N HN) P)
          with "[] [Raw OA OF P]") as "#CInew".
        { iPureIntro. apply _. }
        { iNext. rewrite /state. iExists None. iFrame. }
        iModIntro. iExists (MkGname gt go gi N HN).
        iSplit; first (iPureIntro; reflexivity).
        rewrite /R /token !_at_sep !_at_pureR !_at_as_Rep /=.
        iFrame "Ty CInew". iFrame.
    Qed.

    Lemma locked_my_mutexes_exclusive (this : ptr) g th q qt P E :
      ↑mutex_inv_namespace g ⊆ E ->
      this |-> R g q P ** locked this g th qt **
        MutexSets.my_mutexes th
          (coPset.CoPset $ ↑mutex_inv_namespace g) |-- (|={E}=> False).
    Proof.
      intros Hmask. rewrite /R /locked !_at_sep !_at_pureR !_at_as_Rep.
      iIntros "((_ & #HI & HO) & HF & Hnames)".
      iInv "HI" as "[(%owner & _ & >HA & HS) HO]".
      iDestruct (observe_2 [|owner = Some (th, qt)|] with "HA HF") as %->.
      iDestruct "HS" as ">HS". rewrite /not_locked.
      iDestruct "HS" as "[Htok Hheld]".
      iDestruct (MutexSets.my_mutexes_exclusive with "[$Hheld $Hnames]") as %[].
      have Hnonempty := nclose_non_empty (mutex_inv_namespace g). set_solver.
    Qed.
  End with_cpp.

  #[global] Hint Opaque not_locked : sl_opacity typeclass_instances.
End MutexPreds.

Module mutex.
  Include MutexPreds.
  Abbreviation EBUSY := pthread_errno.EBUSY (only parsing).

  Module Spec := pthread_mutex_spec MutexPreds.

  #[global] Instance R_pthread_type_ptr
      `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ, !HasStdThreads Σ} g q P :
    Observe (type_ptrR "pthread_mutex_t") (R g q P).
  Proof. apply R_type_ptr. Qed.

  (** A full lifetime token excludes an owner, which has deposited a positive
      share. Destruction also needs the full R share: that additionally rules
      out pending calls, including threads blocked in lock. *)
  Lemma locked_full_token
      `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ, !HasStdThreads Σ}
      (this : ptr) g q P th qt :
    this |-> R g q P ** token g 1$m ** locked this g th qt |--
      (|={⊤}=> False).
  Proof.
    rewrite /R /locked !_at_sep !_at_pureR !_at_as_Rep.
    iIntros "((_ & #HI & HO) & HT & HF)".
    iInv "HI" as "[(%owner & _ & >HA & HS) HO]".
    iDestruct (observe_2 [|owner = Some (th, qt)|] with "HA HF") as %->.
    iDestruct "HS" as ">HS". rewrite /not_locked /token.
    iDestruct "HS" as "[Held Hmine]".
    iDestruct (MutexTokens.token_valid_2 with "[$HT $Held]") as %Hbad.
    exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt) Hbad).
  Qed.

  (** The ordinary acquisition contracts are registered last and are the
      defaults selected by verify/go. Clients of an alternative rule can
      select it in a local Section with e.g.
      [Definition owned_lock := RegisterSpec lock_owned_spec] followed by
      [#[local] Existing Instance owned_lock]. *)
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.
    Context `{!mutex_set_G Σ, !G Σ}.

    (** glibc's default initialization path has no error return. Failed,
        invalid, or nondefault initialization is not described. *)
    cpp.spec "pthread_mutex_init" as init_spec from source with
      (\exact Unfold MutexPreds.cpp_ty (Reduce Spec.init_spec)).

    cpp.spec "pthread_mutex_destroy" as destroy_spec from source with
      (\exact Unfold MutexPreds.cpp_ty (Reduce Spec.destroy_spec)).

    cpp.spec "pthread_mutex_lock" as lock_owned_spec from source with
      (\exact Reduce Spec.lock_owned_spec).

    cpp.spec "pthread_mutex_lock" as lock_spec from source with
      (\exact Reduce Spec.lock_spec).

    cpp.spec "pthread_mutex_unlock" as unlock_spec from source with
      (\exact Reduce Spec.unlock_spec).

    cpp.spec "pthread_mutex_trylock" as trylock_owned_spec from source with
      (\exact Reduce Spec.trylock_owned_spec).

    cpp.spec "pthread_mutex_trylock" as trylock_held_spec from source with
      (\exact Reduce Spec.trylock_held_spec).

    cpp.spec "pthread_mutex_trylock" as trylock_uncontended_spec from source with
      (\exact Reduce Spec.trylock_uncontended_spec).

    cpp.spec "pthread_mutex_trylock" as trylock_spec from source with
      (\exact Reduce Spec.trylock_spec).

    (** Linux/glibc ABI setup rule. On the target x86_64 ABI,
        PTHREAD_MUTEX_INITIALIZER and a zero-initialized global both contain
        the zero bytes of a default mutex. This consumes the exclusive raw
        bytes ONCE, rather than reinterpreting an existing R predicate or
        permitting reinitialization. POSIX alone does not justify zero setup.
        zeroR includes ownership of the complete sizeof(pthread_mutex_t)
        byte region; padding is covered too. type_ptrR additionally requires
        a suitable typed and aligned object, rather than an arbitrary byte
        array of the same size. *)
    Axiom setup_zero : forall (this : ptr) (N : namespace) (P : mpred),
      N <> nroot -> WeaklyObjective P ->
      this |-> type_ptrR "pthread_mutex_t" **
      this |-> zeroR "pthread_mutex_t" 1$m ** ▷P |--
        (|={⊤}=> ∃ g, [| mutex_inv_namespace g = N |] **
          this |-> R g 1$m P ** token g 1$m).

    (** The initializer macro has the same physical representation on this
        ABI. Both setup paths use the same exclusive, one-shot rule. *)
    Definition setup_initializer := setup_zero.
  End with_cpp.

  #[global] Hint Opaque R token not_locked locked state : sl_opacity typeclass_instances.
End mutex.
End pthread.
