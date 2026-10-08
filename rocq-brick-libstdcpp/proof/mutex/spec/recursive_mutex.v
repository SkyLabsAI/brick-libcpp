Require Import iris.algebra.gset.
Require Import iris.algebra.coPset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

(** * This file contains:
      - The logical states [RecursiveMutexState]
      - The predicate interface [RECURSIVE_MUTEX_PREDS]
      - Recursive mutex specs that are parametric to their C++ names
        [recursive_mutex_spec]
      - And specs that are bound to stdlib names [StdRecursiveMutex] *)

(** The C++ class a recursive-mutex specification is stated at. *)
Module Type MutexCPPName.
  Parameter cpp_ty : type.
End MutexCPPName.

(** Logical state of the recursive mutex.
    A recursive mutex starts in NotHeld, lock increment the held count,
    and unlock decrements it:
      NotHeld <-> Held 0 _ <-> Held 1 _ <-> ... *)
Module RecursiveMutexState.
  Inductive acquire_state {TT : tele} : Type :=
  | NotHeld                (* not held *)
  | Held (n : nat) (xs : TT) (* acquired [n + 1] times with quantifiers [xs] *).
  #[global] Arguments acquire_state _ : clear implicits.

  sl.lock
  Definition acquire {TT} (a a' : acquire_state TT) : Prop :=
    match a with
    | NotHeld => exists xs, a' = Held 0 xs
    | Held n xs => a' = Held (S n) xs
    end.

  Lemma acquire_NotHeld_Held0 TT args :
    acquire NotHeld (Held (TT := TT) 0 args).
  Proof. by rewrite acquire.unlock; eauto. Qed.

  Lemma acquire_Held_S TT n xs :
    acquire (Held (TT := TT) n xs) (Held (S n) xs).
  Proof. by rewrite acquire.unlock. Qed.

  #[global] Hint Resolve acquire_NotHeld_Held0 : br_hints.
  #[global] Hint Resolve acquire_Held_S : br_hints.

  sl.lock
  Definition release {TT} (a : acquire_state TT) : acquire_state TT :=
    match a with
    | NotHeld => NotHeld (* unreachable *)
    | Held n xs =>
        match n with
        | 0 => NotHeld
        | S n => Held n xs
        end
    end.

  Lemma is_held {TT : tele} {t1 t2 : acquire_state TT} :
    acquire t1 t2 ->
    ∃ n xs, t2 = Held n xs /\ t1 = release t2.
  Proof.
    rewrite acquire.unlock release.unlock.
    intros. destruct t1; simpl in H; eauto.
    - exists 0. naive_solver.
    - exists (S n). naive_solver.
  Qed.

  Definition update {TT : tele} (f : TT -t> TT)
      (x : acquire_state TT) : acquire_state TT :=
    match x with
    | NotHeld => NotHeld
    | Held n xs => Held n (tele_app f xs)
    end.

  Lemma update_eq {TT : tele} f t1 t2 : acquire t1 t2 ->
      update f t1 = release (TT := TT) (update f t2).
  Proof.
    by intros ([|] & ? & -> & ->)%is_held; rewrite !release.unlock.
  Qed.
End RecursiveMutexState.

(** Predicates of a recursive_mutex. *)
Module Type RECURSIVE_MUTEX_PREDS (T : MutexCPPName).
  Include RecursiveMutexState.
  Definition cpp_ty : type := T.cpp_ty.
  Parameter gname : Set.
  Parameter G : forall `{Σ : cpp_logic}, Type.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.

  (** Ghost name of the ghost state that keeps track of a pool of gnames for each thread. *)
  Parameter pool_name : gname -> iprop.gname.
  Parameter rmutex_inv_namespace : gname -> namespace.
  #[global] Declare Instance sets_G `{Σ : cpp_logic, !G Σ} : MutexSets.G Σ.
  Parameter token : forall `{Σ : cpp_logic, !G Σ}, gname -> cQp.t -> mpred.
  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} g : CFractional (token g).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} g qt : Timeless (token g qt).

  Parameter not_locked : forall `{Σ : cpp_logic, !G Σ, σ : genv},
    ptr -> gname -> cQp.t -> thread_idT -> mpred.
  Parameter locked : forall `{Σ : cpp_logic, !G Σ, σ : genv},
    ptr -> gname -> cQp.t -> thread_idT -> nat -> mpred.

  (* abstract predicate of owership of a recursive mutex that protects some
     resource [P], e.g. in the form of [inv _ P]. Note that it only represents
     the mutex data structure, not the ownership of [P]. *)
  Parameter R : forall `{Σ : cpp_logic, !G Σ}
    {HAS_THREADS : HasStdThreads Σ} {σ : genv},
    gname -> cQp.t -> mpred -> Rep.
  #[global] Hint Opaque token not_locked locked R : sl_opacity typeclass_instances.

  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.

    #[global] Declare Instance not_locked_timeless {σ : genv} this g qt th :
      Timeless (not_locked this g qt th).

    Context {HAS_THREADS : HasStdThreads Σ} {σ : genv}.

    #[global] Declare Instance locked_timeless this g qt th n :
      Timeless (locked this g qt th n).

    #[only(cfractional,cfracvalid,ascfractional)] derive R.
    #[global] Declare Instance R_type_ptr g q P : Observe (type_ptrR cpp_ty) (R g q P).

    (** FIXME maybe not_locked should just be a definition in the spec section? *)
    Parameter register_thread : forall
        (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t),
      token g qt ** MutexSets.my_mutexes (pool_name g) th
        (CoPset $ ↑rmutex_inv_namespace g) ⊣⊢
      not_locked this g qt th.

  End with_cpp.
End RECURSIVE_MUTEX_PREDS.

(** Shared contracts, [BasicLockable] presentation, and proof automation. *)
Module recursive_mutex_spec (T : MutexCPPName)
    (Preds : RECURSIVE_MUTEX_PREDS T).
  Import Preds RecursiveMutexState.
  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.
    Context {HAS_THREADS : HasStdThreads Σ} {σ : genv}.

    Definition acquireable (this : ptr) (g : gname) (qt : cQp.t)
        (th : thread_idT) {TT : tele} (s : acquire_state TT)
        (P : TT -t> mpred) : mpred :=
      current_thread th **
      match s with
      | NotHeld => not_locked this g qt th
      | Held n xs => locked this g qt th n ** tele_app P xs
      end.
    #[global] Hint Opaque acquireable : sl_opacity typeclass_instances.

    #[global] Instance acquireable_current_thread this g qt th TT s P :
      Observe (current_thread th) (acquireable this g qt th (TT := TT) s P).
    Proof. rewrite /acquireable. apply _. Qed.

    Definition lock_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{g TT P q} this |-> R g q (∃ xs, tele_app (TT := TT) P xs)
       \pre{qt th n} acquireable this g qt th n P
       \post Exists n', [| acquire n n' |] ** ▷ acquireable this g qt th n' P).

    Definition unlock_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{g TT P q} this |-> R g q (∃ xs, tele_app (TT := TT) P xs)
       \pre{qt th n args} acquireable this g qt th (Held n args) P
       \post acquireable this g qt th (release $ Held n args) P).

    Definition do_lock (this : ptr) (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ TT P qt th n,
        [| lk.2 = (∃ xs, tele_app (TT := TT) P xs)%I |] **
        acquireable this lk.1 qt th n P **
        ((* TODO readd *)
         (* ▷ *)
          (Exists n', [| acquire n n' |] ** ▷ acquireable this lk.1 qt th n' P) -* K).
    #[global] Arguments do_lock /.

    Definition do_unlock (this : ptr) (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ TT P qt th n args,
        [| lk.2 = (∃ xs, tele_app (TT := TT) P xs)%I |] **
        acquireable this lk.1 qt th (Held n args) P **
        ((* TODO readd *)
        (* ▷ *)
        acquireable this lk.1 qt th (release $ Held n args) P -* K).
    #[global] Arguments do_unlock /.

    #[global] Instance recursive_mutex_basic_lockable : BasicLockable
      (T := gname * mpred) cpp_ty (fun q gP => R gP.1 q gP.2) :=
      { do_lock := do_lock
      ; do_unlock := do_unlock }.

    Definition lock_spec_alt : ptr -> WpSpec mpred val val :=
      lock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).
    Definition unlock_spec_alt : ptr -> WpSpec mpred val val :=
      unlock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

    Lemma lock_spec_equiv_lock_spec_alt this xs K :
      lock_spec this xs K ⊣⊢ lock_spec_alt this xs K.
    Proof.
      unfold lock_spec, lock_spec_alt, lock_basic_lockable, do_lock.
      cbn. iSplit.
      - iIntros "H". iDestruct "H" as (g TT P q qt th n)
          "(%Hxs & HR & HA & HK)".
        iExists q, (g, (∃ xs, tele_app P xs)%I),
          (Exists n', [| acquire n n' |] ** ▷ acquireable this g qt th n' P)%I.
        iFrame "HR HK". iSplit; first done.
        iExists TT, P, qt, th, n. iFrame "HA".
        iSplit; first done. iIntros "$".
      - iIntros "H". iDestruct "H" as (q [g J] K')
          "(%Hxs & HR & Hdo & HK)".
        iDestruct "Hdo" as (TT P qt th n) "(%Heq & HA & Hcont)".
        simpl in *. subst J.
        iExists g, TT, P, q, qt, th, n. iFrame "HR HA".
        iSplit; first done. iIntros "[HR Hac]".
        iApply "HK". iFrame "HR". iApply "Hcont". iExact "Hac".
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt this xs K :
      unlock_spec this xs K ⊣⊢ unlock_spec_alt this xs K.
    Proof.
      unfold unlock_spec, unlock_spec_alt, unlock_basic_lockable, do_unlock.
      cbn. iSplit.
      - iIntros "H". iDestruct "H" as (g TT P q qt th n args)
          "(%Hxs & HR & HA & HK)".
        iExists q, (g, (∃ xs, tele_app P xs)%I),
          (acquireable this g qt th (release $ Held n args) P).
        iFrame "HR HK". iSplit; first done.
        iExists TT, P, qt, th, n, args. iFrame "HA".
        iSplit; first done. iIntros "$".
      - iIntros "H". iDestruct "H" as (q [g J] K')
          "(%Hxs & HR & Hdo & HK)".
        iDestruct "Hdo" as (TT P qt th n args) "(%Heq & HA & Hcont)".
        simpl in *. subst J.
        iExists g, TT, P, q, qt, th, n, args. iFrame "HR HA".
        iSplit; first done. iIntros "[HR Hac]".
        iApply "HK". iFrame "HR". iApply "Hcont". iExact "Hac".
    Qed.

    Definition ctor_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \pre{pool N TT P xs} |> tele_app (TT := TT) P xs
       \require ∀ xs, Objective (tele_app P xs)
       \post Exists g,
         [| pool_name g = pool /\ rmutex_inv_namespace g = N |] **
         this |-> R g 1$m (∃ xs, tele_app P xs) ** token g 1$m).

    Definition dtor_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \pre{g TT P} this |-> R g 1 (∃ xs, tele_app (TT := TT) P xs)
       \pre token g 1$m
       \post |> (Exists xs, tele_app (TT := TT) P xs)).

    Section proof_automation.
      #[global] Instance R_learn :
        Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
      Proof. solve_learnable. Qed.
      (** Recover the resource telescope before matching its arguments. *)
      #[global] Instance R_learn_TT : `{Learnable
        (R g q1 (∃ xs : tele_arg TT1, tele_app P1 xs))
        (R g q2 (∃ xs : tele_arg TT2, tele_app P2 xs))
        [TT2 = TT1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance R_learn_P TT : `{Learnable
        (R g q1 (∃ xs : tele_arg TT, tele_app P1 xs))
        (R g q2 (∃ xs : tele_arg TT, tele_app P2 xs))
        [P2 = P1] }.
      Proof. solve_learnable. Qed.

      (** The mutex representation remembers the resource after clients open it. *)
      #[global] Instance R_acquireable_learn_TT (this : ptr) : `{Learnable
        (this |-> R g q (∃ xs : tele_arg TT1, tele_app P1 xs))
        (acquireable this g qt th (TT := TT2) t P2)
        [TT2 = TT1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance R_acquireable_learn_P TT (this : ptr) : `{Learnable
        (this |-> R g q (∃ xs : tele_arg TT, tele_app P1 xs))
        (acquireable this g qt th (TT := TT) t P2)
        [P2 = P1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance acquireable_learn_TT : `{Learnable
        (acquireable this g qt1 th (TT := TT1) t1 P1)
        (acquireable this g qt2 th (TT := TT2) t2 P2)
        [qt2 = qt1; TT2 = TT1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance acquireable_learn this γ th TT :
        LearnEq3 (fun qt s P => acquireable this γ qt th (TT := TT) s P).
      Proof. solve_learnable. Qed.
      #[global] Instance not_locked_learn this γ th : LearnEq1 (fun qt => not_locked this γ qt th).
      Proof. solve_learnable. Qed.
      #[global] Instance locked_learn this γ th : LearnEq2 (fun qt n => locked this γ qt th n).
      Proof. solve_learnable. Qed.
      #[global] Instance later_acquireable_learn this γ th TT :
        LearnEq3 (fun qt a b => bi_later (acquireable this γ qt th (TT := TT) a b)).
      Proof. solve_learnable. Qed.

      #[global] Instance : `{Learnable
        (current_thread th)
        (acquireable this (TT := TT0) γ qt th0 args P0)
        [th0 = th] }.
      Proof. solve_learnable. Qed.

      #[global] Instance learn_args (this : ptr)
        {TT : tele} (t : acquire_state TT) (P : TT -t> mpred) :
        `{Learnable
          (tele_app P args ** locked this γ qt th n)
          (acquireable this γ qt' th t P)
          [qt' = qt; t = Held n args] }.
      Proof. solve_learnable. Qed.

      #[global] Instance locked_acquireable_learn {TT : tele} : `{Learnable
        (locked this g qt th n)
        (acquireable this (TT := TT) g qt' th (Held n' args) P)
        [qt' = qt; n' = n] }.
      Proof. solve_learnable. Qed.

      Definition acquireable_current_thread_F :=
        ltac:(mk_obs_fwd acquireable_current_thread).

      #[program]
      Definition acquireable_is_acquired_C {TT} this g qt th t t' P
          (_ : acquire (TT := TT) t t') :=
        \cancelx
        \consuming acquireable this g qt th t' P
        \deduce{args} tele_app P args
        \deduce{n} [| t' = Held n args /\ t = release t' |]
        \deduce locked this g qt th n
        \end.
      Next Obligation.
        intros * (? & ? & -> & ->)%is_held.
        rewrite /acquireable /=. ego.
      Qed.

      #[program]
      Definition acquireable_acquireable_C this γ :=
        \cancelx
        \consuming{qt th n TT args P} acquireable this (TT := TT) γ qt th (Held n args) P
        \bound P'
        \bound_existential qt' th' args'
        \proving acquireable this γ qt' th' args' P'
        \instantiate qt' := qt
        \instantiate th' := th
        \instantiate args' := Held n args
        \deduce tele_app P args
        \through tele_app P' args
        \end.
      Next Obligation. intros. rewrite /acquireable /=; work. Qed.

      #[program]
      Definition own_P_is_acquireable_C {TT} this g qt n P :=
        \cancelx
        \preserving{th} current_thread th
        \consuming locked this g qt th n
        \bound n' args
        \proving acquireable this (TT := TT) g qt th (Held n' args) P
        \through tele_app P args
        \through [| n' = n |]
        \end.
      Next Obligation.
        intros. iIntros "[#Hth Htoken]" (n' args) "[HP %Heq]".
        subst n'. rewrite /acquireable /=. iFrame "#∗".
      Qed.
    End proof_automation.
  End with_cpp.

  #[global] Hint Resolve acquireable_acquireable_C acquireable_is_acquired_C
    own_P_is_acquireable_C acquireable_current_thread_F : br_hints.
End recursive_mutex_spec.

Module StdRecursiveMutexName.
  Definition cpp_ty : type := "std::recursive_mutex"%cpp_type.
  #[global] Hint Opaque cpp_ty : sl_opacity.
  Definition cpp_N : bs := "std::recursive_mutex".
End StdRecursiveMutexName.


(** Bind the reusable specifications to std::recursive_mutex names, but with 
    a parametrized RECURSIVE_MUTEX_PREDS. *)
Module StdRecursiveMutex
    (Preds : RECURSIVE_MUTEX_PREDS StdRecursiveMutexName).
  Include Preds.
  #[global] Hint Opaque cpp_ty : sl_opacity.
  Module Spec := recursive_mutex_spec StdRecursiveMutexName Preds.
  Include Spec.

  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context `{MOD : source ⊧ σ}.

    cpp.spec "std::recursive_mutex::recursive_mutex()" as std_ctor_spec with
      (\exact Reduce Spec.ctor_spec).
    cpp.spec "std::recursive_mutex::~recursive_mutex()" as std_dtor_spec with
      (\exact Reduce Spec.dtor_spec).
    cpp.spec "std::recursive_mutex::lock()" as std_lock_spec with
      (\exact Reduce Spec.lock_spec).
    cpp.spec "std::recursive_mutex::unlock()" as std_unlock_spec with
      (\exact Reduce Spec.unlock_spec).
    cpp.spec "std::recursive_mutex::lock()" as std_lock_spec_alt with
      (\exact Reduce Spec.lock_spec_alt).
    cpp.spec "std::recursive_mutex::unlock()" as std_unlock_spec_alt with
      (\exact Reduce Spec.unlock_spec_alt).

    Lemma std_lock_spec_equiv_std_lock_spec_alt : std_lock_spec -|- std_lock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; intros this xs K;
        rewrite Spec.lock_spec_equiv_lock_spec_alt; done.
    Qed.
    Lemma std_unlock_spec_equiv_std_unlock_spec_alt : std_unlock_spec -|- std_unlock_spec_alt.
    Proof.
      iSplit; iApply specify_mono; intros this xs K;
        rewrite Spec.unlock_spec_equiv_unlock_spec_alt; done.
    Qed.
  End with_cpp.
End StdRecursiveMutex.

(** The standard-library implementation remains abstract; concrete recursive
    mutex implementations supply their own [RECURSIVE_MUTEX_PREDS]. *)
Declare Module RecursiveMutexPreds : RECURSIVE_MUTEX_PREDS StdRecursiveMutexName.
Module std_recursive_mutex := StdRecursiveMutex RecursiveMutexPreds.
