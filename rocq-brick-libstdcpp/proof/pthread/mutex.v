(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * SPDX-License-Identifier: BSD-3-Clause
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.zeroR.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.

Import linearity.
Export lock_ghost2.mutex_set_G (mutex_set_G).

Module pthread.
Export skylabs.brick.libstdcpp.pthread.pred.pthread.
Module mutex.
  (** Linux/glibc's default mutex: NORMAL, process-private, non-robust,
      PTHREAD_PRIO_NONE. These are trusted library specifications, not proofs
      of glibc's implementation. No recursive, robust, process-shared, or
      priority-protection attribute is covered by this representation.

      In particular, glibc maps DEFAULT to NORMAL. Relocking by its owner
      blocks forever; trylock instead returns EBUSY, including for its owner.
      An exclusive, uncontended trylock rule below excludes spurious failure.
      EBUSY is 16 in the Linux ABI used by this library's toolchain. *)
  Definition EBUSY : Z := 16.

  Record gname : Set := MkGname {
    token_gname : iprop.gname;
    owner_gname : iprop.gname;
    inv_gname : iprop.gname;
    mutex_inv_namespace : namespace;
    mutex_inv_namespace_not_root : mutex_inv_namespace <> nroot;
  }.

  Class G `{Σ : cpp_logic} := {
    #[global] tokens_G :: MutexTokens.G Σ;
    #[global] owners_G :: OwnerTid.G Σ;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition token `{Σ : cpp_logic, !G Σ} (g : gname) (q : cQp.t) : mpred :=
    MutexTokens.token g.(token_gname) (cQp.frac q).
  #[global] Instance token_fractional `{Σ : cpp_logic, !G Σ} g :
      CFractional (token g).
  Proof. intros q1 q2. rewrite /token cQp.frac_add. apply MutexTokens.token_fractional. Qed.
  #[global] Instance token_timeless `{Σ : cpp_logic, !G Σ} g q :
      Timeless (token g q).
  Proof. rewrite /token. apply _. Qed.

  Definition not_locked `{Σ : cpp_logic, !mutex_set_G Σ, !G Σ}
      (_this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    token g qt ** MutexSets.my_mutexes th (coPset.CoPset $ ↑g.(mutex_inv_namespace)).

  Definition locked `{Σ : cpp_logic, !G Σ}
      (_this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    OwnerTid.owner_tid_frag g.(owner_gname) (Some (th, qt)).

  #[global] Instance not_locked_learn `{Σ : cpp_logic, !mutex_set_G Σ, !G Σ} this g th :
      LearnEq1 (not_locked this g th).
  Proof. solve_learnable. Qed.
  #[global] Instance locked_learn `{Σ : cpp_logic, !G Σ} this g th :
      LearnEq1 (locked this g th).
  Proof. solve_learnable. Qed.

  (** Exclusive physical ownership of the default pthread mutex. Its boolean
      records whether it is held. Its bytes are hidden behind the invariant:
      clients cannot inspect or copy an initialized mutex. The representation
      is deliberately independent of the std::mutex function specifications. *)
  Parameter rawR : forall `{Σ : cpp_logic, σ : genv}, bool -> Rep.

  Definition state `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (this : ptr) (g : gname) (P : mpred) : mpred :=
    ∃ owner : option (thread_idT * cQp.t),
      this |-> rawR (bool_decide (is_Some owner)) **
      OwnerTid.owner_tid_auth g.(owner_gname) owner **
      match owner with
      | None => OwnerTid.owner_tid_frag g.(owner_gname) None ** P
      | Some (th, qt) => not_locked this g th qt
      end.

  Definition R `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (g : gname) (q : cQp.t) (P : mpred) : Rep :=
    type_ptrR "pthread_mutex_t" **
    as_Rep (fun this => cinv g.(mutex_inv_namespace) g.(inv_gname) (state this g P)) **
    pureR (cinv_own g.(inv_gname) q).
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(cfractional,cfracvalid,ascfractional)] derive R.
  #[global] Instance R_type_ptr `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ} g q P :
      Observe (type_ptrR "pthread_mutex_t") (R g q P).
  Proof. rewrite /R. apply _. Qed.
  #[global] Instance R_learnable `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ} :
    Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
  Proof. solve_learnable. Qed.
  #[global] Instance locked_timeless `{Σ : cpp_logic, !G Σ} this g th qt :
      Timeless (locked this g th qt).
  Proof. rewrite /locked. apply _. Qed.
  #[global] Instance not_locked_timeless `{Σ : cpp_logic, !mutex_set_G Σ, !G Σ} this g th qt :
      Timeless (not_locked this g th qt).
  Proof. rewrite /not_locked. apply _. Qed.
  #[global] Instance locked_exclusive `{Σ : cpp_logic, !G Σ} this g :
      Exclusive2 (locked this g).
  Proof. intros th1 th2 qt1 qt2. rewrite /locked. apply _. Qed.
  #[global] Instance not_locked_exclusive `{Σ : cpp_logic, !mutex_set_G Σ, !G Σ} this g th :
      Exclusive1 (not_locked this g th).
  Proof.
    intros q1 q2. rewrite /not_locked. iIntros "[_ H1] [_ H2]".
    have Hoverlap : ~ ((↑g.(mutex_inv_namespace) : coPset) ## ↑g.(mutex_inv_namespace)).
    { have Hnonempty := nclose_non_empty g.(mutex_inv_namespace). set_solver. }
    iDestruct (MutexSets.my_mutexes_exclusive _ _ _ Hoverlap with "[$H1 $H2]") as %[].
  Qed.

  (** A full lifetime token excludes an owner, which has deposited a positive
      share. Destruction also needs the full R share: that additionally rules
      out pending calls, including threads blocked in lock. *)
  Lemma locked_full_token `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (this : ptr) g q P th qt :
    this |-> R g q P ** token g 1$m ** locked this g th qt |--
      (|={⊤}=> False).
  Proof.
    rewrite /R /locked !_at_sep !_at_pureR !_at_as_Rep.
    iIntros "((_ & #HI & HO) & HT & HF)".
    iInv g.(mutex_inv_namespace) as "[(%owner & _ & >HA & HS) HO]".
    iDestruct (observe_2 [|owner = Some (th, qt)|] with "HA HF") as %->.
    iDestruct "HS" as "[>Held _]".
    rewrite /token.
    iDestruct (MutexTokens.token_valid_2 with "[$HT $Held]") as %Hbad.
    exfalso. exact (Qp.not_add_le_l 1 (cQp.frac qt) Hbad).
  Qed.

  (** The previous mutex-spec regressions concerned precisely this exclusion:
      an owner cannot also retain permission for a fresh acquisition. *)
  Lemma locked_not_locked_exclusive
      `{Σ : cpp_logic, σ : genv, !mutex_set_G Σ, !G Σ}
      (this : ptr) g q P th qt qt' :
    this |-> R g q P ** locked this g th qt ** not_locked this g th qt' |--
      (|={⊤}=> False).
  Proof.
    rewrite /R /locked /not_locked !_at_sep !_at_pureR !_at_as_Rep.
    iIntros "((_ & #HI & HO) & HF & _ & Hnames)".
    iInv g.(mutex_inv_namespace) as "[(%owner & _ & >HA & HS) HO]".
    iDestruct (observe_2 [|owner = Some (th, qt)|] with "HA HF") as %->.
    iDestruct "HS" as "[_ >Hheld]".
    iDestruct (MutexSets.my_mutexes_exclusive with "[$Hheld $Hnames]") as %[].
    have Hnonempty := nclose_non_empty g.(mutex_inv_namespace). set_solver.
  Qed.

  (** The ordinary acquisition contracts are registered last and are the
      defaults selected by verify/go. Clients of an alternative rule can
      select it in a local Section with e.g.
      [Definition owned_lock := RegisterSpec lock_owned_spec] followed by
      [#[local] Existing Instance owned_lock]. *)
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.
    Context `{!mutex_set_G Σ, !G Σ}.

    (** glibc's default initialization path has no error return. Ownership of
        the entire storage excludes initialization of a live mutex and any
        concurrent access. Failed, invalid, or nondefault initialization is
        not described by this contract. *)
    cpp.spec "pthread_mutex_init" as init_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \pre this |-> anyR "pthread_mutex_t" 1$m
      \arg "mutexattr" (Vptr nullptr)
      \pre{N P} ▷P
      \require N <> nroot
      \require WeaklyObjective P
      \post[Vint 0] |={⊤}=> ∃ g,
        [| g.(mutex_inv_namespace) = N |] **
        this |-> R g 1$m P ** token g 1$m).

    cpp.spec "pthread_mutex_destroy" as destroy_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \pre{g P} this |-> R g 1$m P ** token g 1$m
      \post[Vint 0] this |-> anyR "pthread_mutex_t" 1$m ** P).

    (** Defined non-return under partial correctness, not undefined behavior.
        P can be framed; it is not consumed by relocking. *)
    cpp.spec "pthread_mutex_lock" as lock_owned_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g q P} this |-> R g q P
      \persist{th} current_thread th
      \pre{qt} locked this g th qt
      \post{ret : Z}[Vint ret] False).

    cpp.spec "pthread_mutex_lock" as lock_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g q P} this |-> R g q P
      \persist{th} current_thread th
      \pre{qt} not_locked this g th qt
      \post[Vint 0] locked this g th qt ** P).

    cpp.spec "pthread_mutex_unlock" as unlock_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g q P} this |-> R g q P
      \persist{th} current_thread th
      \pre{qt} locked this g th qt
      \pre ▷P
      \post[Vint 0] not_locked this g th qt).

    cpp.spec "pthread_mutex_trylock" as trylock_owned_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g q P} this |-> R g q P
      \persist{th} current_thread th
      \prepost{qt} locked this g th qt
      \post[Vint EBUSY] emp).

    (** A held token may be temporarily handed to another thread for this
        observation. The owner cannot unlock concurrently without that token,
        so trylock definitely returns EBUSY, whichever thread calls it. No
        acquisition permission is needed and no ownership is granted. *)
    cpp.spec "pthread_mutex_trylock" as trylock_held_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g q P} this |-> R g q P
      \prepost{owner qt} locked this g owner qt
      \post[Vint EBUSY] emp).

    (** Full R excludes another active call, and the full lifetime token
        contained in not_locked excludes any owner. Thus acquisition really
        succeeds, rather than exhibiting std::mutex's spurious failure. In
        the shared rule, EBUSY does not imply the mutex is still held at
        return: an interfering owner may already have released it. *)
    cpp.spec "pthread_mutex_trylock" as trylock_uncontended_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g P} this |-> R g 1$m P
      \persist{th} current_thread th
      \pre not_locked this g th 1$m
      \post[Vint 0] locked this g th 1$m ** P).

    cpp.spec "pthread_mutex_trylock" as trylock_spec from source with (
      \arg{this} "mutex" (Vptr this)
      \prepost{g q P} this |-> R g q P
      \persist{th} current_thread th
      \pre{qt} not_locked this g th qt
      \post{success : bool}[Vint (if success then 0 else EBUSY)]
        if success then locked this g th qt ** P
        else not_locked this g th qt).

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
        (|={⊤}=> ∃ g, [| g.(mutex_inv_namespace) = N |] **
          this |-> R g 1$m P ** token g 1$m).

    (** The initializer macro has the same physical representation on this
        ABI. Both setup paths use the same exclusive, one-shot rule. *)
    Definition setup_initializer := setup_zero.
  End with_cpp.

  #[global] Hint Opaque R token not_locked locked state : sl_opacity typeclass_instances.
End mutex.
End pthread.
