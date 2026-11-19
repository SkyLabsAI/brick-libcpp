(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * SPDX-License-Identifier: BSD-3-Clause
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.zeroR.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Export skylabs.brick.libstdcpp.mutex.spec.base_mutex.
Require Export skylabs.brick.libstdcpp.mutex.spec.owner_tid_mutex.

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
  Include OwnerTidMutex.
  Definition cpp_ty : type := "pthread_mutex_t".

  (** Exclusive physical ownership of the default pthread mutex. Its boolean
      records whether it is held. Its bytes are hidden behind the invariant:
      clients cannot inspect or copy an initialized mutex. Like every physical
      points-to, it does not depend on the thread's view. *)
  Parameter rawR : forall `{Σ : cpp_logic, σ : genv}, bool -> Rep.
  Axiom rawR_weakly_objective : forall `{Σ : cpp_logic, σ : genv} (this : ptr) b,
    WeaklyObjective (this |-> rawR b).
  #[global] Existing Instance rawR_weakly_objective.

  Definition raw `{Σ : cpp_logic, σ : genv} (this : ptr) (b : bool) : mpred :=
    this |-> rawR b.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.

    Definition R {HAS_THREADS : HasStdThreads Σ} {σ : genv}
        (g : gname) (q : cQp.t) (P : mpred) : Rep :=
      type_ptrR "pthread_mutex_t" **
      as_Rep (fun this => cinv (mutex_inv_namespace g) g.(inv_gname) (state raw this g P)) **
      pureR (cinv_own g.(inv_gname) q).
    #[global] Hint Opaque R : sl_opacity typeclass_instances.
    #[only(cfractional,cfracvalid,ascfractional)] derive R.

    Lemma R_mutexR {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P :
      R g q P = mutexR (fun _ => type_ptrR "pthread_mutex_t") raw g q P.
    Proof. reflexivity. Qed.

    #[global] Instance R_type_ptr {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P :
      Observe (type_ptrR cpp_ty) (R g q P).
    Proof. rewrite /R /cpp_ty. apply _. Qed.
    #[global] Instance R_learnable {HAS_THREADS : HasStdThreads Σ} {σ : genv} :
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    Context {σ : genv}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    Lemma init_R (this : ptr) (old : gname) (N : namespace) (P : mpred) :
      WeaklyObjective P ->
      N <> nroot ->
      this |-> R old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g,
          [| mutex_inv_namespace g = N |] **
          this |-> R g 1$m P ** token g 1$m).
    Proof.
      intros. by apply (mutexR_reinit (fun _ => type_ptrR "pthread_mutex_t") raw); [apply _|..].
    Qed.

    Lemma locked_my_mutexes_exclusive (this : ptr) g th q qt P E :
      ↑mutex_inv_namespace g ⊆ E ->
      this |-> R g q P ** locked this g th qt **
        MutexSets.my_mutexes th
          (coPset.CoPset $ ↑mutex_inv_namespace g) |-- (|={E}=> False).
    Proof. rewrite R_mutexR. apply mutexR_locked_my_mutexes_exclusive. Qed.
  End with_cpp.
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
  Proof. rewrite R_mutexR. apply mutexR_locked_full_token. Qed.

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

  #[global] Hint Opaque R : sl_opacity typeclass_instances.
End mutex.
End pthread.
