Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

(** * This file contains:
      - The logical states ([RecursiveMutexState])
      - An interface of predicates [RECURSIVE_MUTEX_PREDS]
      - Recursive mutex specs [recursive_mutex_spec]
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

  Parameter used_threads : forall `{Σ : cpp_logic, !G Σ}
    {HAS_THREADS : HasStdThreads Σ}, gname -> gset thread_idT -> mpred.
  Parameter held_token : forall `{Σ : cpp_logic, !G Σ},
    gname -> thread_idT -> nat -> mpred.
  (* [acquireable γ th s P] contains an acquire state [s] and, if the acquire
     state is held, the resource P. *)
  Parameter acquireable : forall `{Σ : cpp_logic, !G Σ}
    {HAS_THREADS : HasStdThreads Σ}, gname -> thread_idT ->
    forall {TT : tele}, acquire_state TT -> (TT -t> mpred) -> mpred.
  (* abstract predicate of owership of a recursive mutex that protects some
     resource [P], e.g. in the form of [inv _ P]. Note that it only represents
     the mutex data structure, not the ownership of [P]. *)
  Parameter R : forall `{Σ : cpp_logic, !G Σ}
    {HAS_THREADS : HasStdThreads Σ} {σ : genv},
    gname -> cQp.t -> mpred -> Rep.
  #[global] Hint Opaque used_threads held_token acquireable R : sl_opacity typeclass_instances.

  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    #[global] Declare Instance held_token_timeless g th n :
      Timeless (held_token g th n).
    #[global] Declare Instance acquireable_current_thread :
      `{Observe (current_thread th) (acquireable g th (TT := TT) t P)}.

    Axiom acquireable_Held : forall g th {TT : tele} n (xs : TT) P,
      acquireable g th (Held n xs) P ⊣⊢
        current_thread th ** held_token g th n ** tele_app P xs.

    Axiom use_thread_acquirable : forall {TT : tele} th g m P,
      th ∉ m ->
      current_thread th ** used_threads g m |-- (|==>
        used_threads g (m ∪ {[th]}) ** acquireable (TT := TT) g th NotHeld P).

    Axiom logout_acquirable : forall {TT : tele} th g m P,
      th ∉ m ->
      used_threads g (m ∪ {[th]}) ** acquireable (TT := TT) g th NotHeld P |--
        (|==> used_threads g m).

    Context {σ : genv}.
    #[only(cfractional,cfracvalid,ascfractional)] derive R.
    #[global] Declare Instance R_type_ptr g q P : Observe (type_ptrR cpp_ty) (R g q P).
  End with_cpp.
End RECURSIVE_MUTEX_PREDS.

(** Non-atomic specifications and their automation use only the public rules. *)
Module recursive_mutex_spec (T : MutexCPPName) (Preds : RECURSIVE_MUTEX_PREDS T).
  Import Preds.
  Section with_cpp.
    Context `{Σ : cpp_logic, !G Σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context {σ : genv}.

    Definition ctor_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \persist{th} current_thread th
       \pre{TT P xs} |> tele_app (TT := TT) P xs
       \require ∀ xs, Objective (tele_app P xs)
       \post Exists g,
         this |-> R g 1$m (∃ xs, tele_app P xs) ** used_threads g empty).

    Definition dtor_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \pre{g TT P} this |-> R g 1 (∃ xs, tele_app (TT := TT) P xs)
       \pre used_threads g empty
       \post |> (Exists xs, tele_app (TT := TT) P xs)).

    Definition lock_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{g TT P q} this |-> R g q (∃ xs, tele_app (TT := TT) P xs)
       \pre{th n} acquireable g th n P
       \post Exists n', [| acquire n n' |] ** ▷ acquireable g th n' P).

    Definition unlock_spec : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{g TT P q} this |-> R g q (∃ xs, tele_app (TT := TT) P xs)
       \pre{th n args} acquireable g th (Held n args) P
       \post acquireable g th (release $ Held n args) P).

    Definition do_lock (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ TT P th n,
        [| lk.2 = (∃ xs, tele_app (TT := TT) P xs)%I |] **
        acquireable lk.1 th n P **
        ((* TODO readd *)
         (* ▷ *)
          (Exists n', [| acquire n n' |] ** ▷ acquireable lk.1 th n' P) -* K).
    #[global] Arguments do_lock /.

    Definition do_unlock (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ TT P th n args,
        [| lk.2 = (∃ xs, tele_app (TT := TT) P xs)%I |] **
        acquireable lk.1 th (Held n args) P **
        ((* TODO readd *)
        (* ▷ *)
        acquireable lk.1 th (release $ Held n args) P -* K).
    #[global] Arguments do_unlock /.

    #[global] Instance recursive_mutex_basic_lockable : BasicLockable
      (T := gname * mpred) cpp_ty (fun q gP => R gP.1 q gP.2) :=
      { do_lock := fun this => do_lock
      ; do_unlock := fun this => do_unlock }.

    Definition lock_spec_alt : ptr -> WpSpec mpred val val :=
      lock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).
    Definition unlock_spec_alt : ptr -> WpSpec mpred val val :=
      unlock_basic_lockable cpp_ty (fun q gP => R gP.1 q gP.2).

    Lemma lock_spec_equiv_lock_spec_alt this xs K :
      lock_spec this xs K ⊣⊢ lock_spec_alt this xs K.
    Proof.
      unfold lock_spec, lock_spec_alt, lock_basic_lockable, do_lock.
      cbn. iSplit.
      - iIntros "H". iDestruct "H" as (g TT P q th n)
          "(%Hxs & HR & HA & HK)".
        iExists q, (g, (∃ xs, tele_app P xs)%I),
          (Exists n', [| acquire n n' |] ** ▷ acquireable g th n' P)%I.
        iFrame "HR HK". iSplit; first done.
        iExists TT, P, th, n. iFrame "HA".
        iSplit; first done. iIntros "$".
      - iIntros "H". iDestruct "H" as (q [g J] K')
          "(%Hxs & HR & Hdo & HK)".
        iDestruct "Hdo" as (TT P th n) "(%Heq & HA & Hcont)".
        simpl in *. subst J.
        iExists g, TT, P, q, th, n. iFrame "HR HA".
        iSplit; first done. iIntros "[HR Hac]".
        iApply "HK". iFrame "HR". iApply "Hcont". iExact "Hac".
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt this xs K :
      unlock_spec this xs K ⊣⊢ unlock_spec_alt this xs K.
    Proof.
      unfold unlock_spec, unlock_spec_alt, unlock_basic_lockable, do_unlock.
      cbn. iSplit.
      - iIntros "H". iDestruct "H" as (g TT P q th n args)
          "(%Hxs & HR & HA & HK)".
        iExists q, (g, (∃ xs, tele_app P xs)%I),
          (acquireable g th (release $ Held n args) P).
        iFrame "HR HK". iSplit; first done.
        iExists TT, P, th, n, args. iFrame "HA".
        iSplit; first done. iIntros "$".
      - iIntros "H". iDestruct "H" as (q [g J] K')
          "(%Hxs & HR & Hdo & HK)".
        iDestruct "Hdo" as (TT P th n args) "(%Heq & HA & Hcont)".
        simpl in *. subst J.
        iExists g, TT, P, q, th, n, args. iFrame "HR HA".
        iSplit; first done. iIntros "[HR Hac]".
        iApply "HK". iFrame "HR". iApply "Hcont". iExact "Hac".
    Qed.

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
        (acquireable g th (TT := TT2) t P2)
        [TT2 = TT1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance R_acquireable_learn_P TT (this : ptr) : `{Learnable
        (this |-> R g q (∃ xs : tele_arg TT, tele_app P1 xs))
        (acquireable g th (TT := TT) t P2)
        [P2 = P1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance acquireable_learn_TT : `{Learnable
        (acquireable g th (TT := TT1) t1 P1)
        (acquireable g th (TT := TT2) t2 P2)
        [TT2 = TT1] }.
      Proof. solve_learnable. Qed.

      #[global] Instance acquireable_learn γ th TT :
        LearnEq2 (acquireable γ th (TT := TT)).
      Proof. solve_learnable. Qed.
      #[global] Instance held_token_learn γ th : LearnEq1 (held_token γ th).
      Proof. solve_learnable. Qed.
      #[global] Instance later_acquireable_learn γ th TT :
        LearnEq2 (fun a b => bi_later (acquireable γ th (TT := TT) a b)).
      Proof. solve_learnable. Qed.

      #[global] Instance : `{Learnable
        (current_thread th)
        (acquireable (TT := TT0) γ th0 args P0)
        [th0 = th] }.
      Proof. solve_learnable. Qed.

      #[global] Instance learn_args
        {TT : tele} (t : acquire_state TT) (P : TT -t> mpred) :
        `{Learnable
          (tele_app P args ** held_token γ th n)
          (acquireable γ th t P)
          [t = Held n args] }.
      Proof. solve_learnable. Qed.

      Definition acquireable_current_thread_F :=
        ltac:(mk_obs_fwd acquireable_current_thread).

      #[program]
      Definition acquireable_is_acquired_C {TT} g th t t' P
          (_ : acquire (TT := TT) t t') :=
        \cancelx
        \consuming acquireable g th t' P
        \deduce{args} tele_app P args
        \deduce{n} [| t' = Held n args /\ t = release t' |]
        \deduce held_token g th n
        \end.
      Next Obligation.
        intros * (? & ? & -> & ->)%is_held.
        rewrite acquireable_Held. ego.
      Qed.

      #[program]
      Definition acquireable_acquireable_C γ :=
        \cancelx
        \consuming{th n TT args P} acquireable (TT := TT) γ th (Held n args) P
        \bound P'
        \bound_existential th' args'
        \proving acquireable γ th' args' P'
        \instantiate th' := th
        \instantiate args' := Held n args
        \deduce tele_app P args
        \through tele_app P' args
        \end.
      Next Obligation. intros. rewrite acquireable_Held; work; rewrite acquireable_Held; work. Qed.

      #[program]
      Definition own_P_is_acquireable_C {TT} g n P :=
        \cancelx
        \preserving{th} current_thread th
        \consuming held_token g th n
        \bound n' args
        \proving acquireable (TT := TT) g th (Held n' args) P
        \through tele_app P args
        \through [| n' = n |]
        \end.
      Next Obligation.
        intros. iIntros "[#Hth Htoken]" (n' args) "[HP %Heq]".
        subst n'. rewrite acquireable_Held. iFrame "#∗".
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

(* export a recursive_mutex module bound to StdRecursiveMutexName but
   RECURSIVE_MUTEX_PREDS is still abstract.*)
Declare Module StdRecursiveMutexPreds : RECURSIVE_MUTEX_PREDS StdRecursiveMutexName.
Module std_recursive_mutex := StdRecursiveMutex StdRecursiveMutexPreds.
