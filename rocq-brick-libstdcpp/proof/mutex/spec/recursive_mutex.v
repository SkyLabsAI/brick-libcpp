Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

Module recursive_mutex.

  (* Not prodO thread_idTO natO. *)
  (* A thread that has zero, locked γ th 0 does not even know which thread has non-0. *)
  Canonical Structure phys_stateUR := authR (optionR (exclR (prodO thread_idTO natO))).

  (** <<locked γ th n>> <<th>> owns the mutex <<γ>> <<n>> times. *)
  Class lockedG `{Σ : cpp_logic} := {
    #[local] has_lock_ghost :: lock_ghost.lockG Σ;

    #[local] has_phys_state :: HasOwn (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_upd :: HasOwnUpd (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_valid :: HasOwnValid (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_unit :: HasOwnUnit mpredI phys_stateUR;
  }.
  #[global] Arguments lockedG {_ _} Σ : assert.

  Record gname : Set := MkGname
  { owned_count_id : iprop.gname;
    locked_gname : iprop.gname;
    inv_gname : iprop.gname;
  }.

  (** [owned_count_id_auth γ Some (th, n)] implies that the lock's count is [n + 1]. *)
  sl.lock
  Definition owned_count_id_auth `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (om : option (thread_idT * natO)) : mpred :=
    own γ.(owned_count_id) (● (option_map Excl om)).
  #[only(timeless)] derive owned_count_id_auth.

  (** [owned_count_id_frag γ Some (th, n)] implies that the lock's count is [n + 1]. *)
  sl.lock
  Definition owned_count_id_frag `{Σ : cpp_logic, !lockedG Σ}
    (γ : gname) (om : option (thread_idT * natO)) : mpred :=
    own γ.(owned_count_id) (◯ (option_map Excl om)).
  #[only(timeless)] derive owned_count_id_frag.

  #[local] Open Scope nat_scope.

  (** [locked γ th n] implies that the lock's count is [n]: see [used_threads]'s
  definition and [owned_count_id_auth]'s informal contract. *)
  sl.lock
  Definition locked `{Σ : cpp_logic, !lockedG Σ}
      (γ : gname) (th : thread_idT) (n : nat) : mpred :=
      users γ.(locked_gname) {[ th ]} **
      match n with
      | 0 => owned_count_id_frag γ None
      | S n => owned_count_id_frag γ (Some (th, n))
      end
  .
  #[only(timeless)] derive locked.

  (* TODO: we should abstract this over the ownership that is produced and
     then it can be used more generally. *)
  sl.lock
  Definition used_threads
    `{Σ : cpp_logic, !lockedG Σ, !HasStdThreads Σ}
    (γ : gname) (s : gset thread_idT) : mpred :=
    lock_ghost.used_threads γ.(locked_gname) s.

  #[only(timeless)] derive used_threads.

  Section locked_with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{!lockedG Σ}.
    Context `{!HasStdThreads Σ}.

    Lemma use_thread th g s :
      th ∉ s ->
      used_threads g s |--
      (|==> used_threads g (s ∪ {[ th ]}) ** locked g th 0).
    Proof.
      rewrite used_threads.unlock locked.unlock.
      iIntros (Hni) "A".
      iMod (lock_ghost.login th g.(locked_gname) s with "A") as "[$ $]";
        first done.
      rewrite owned_count_id_frag.unlock /=.
      iApply own_unit.
    Qed.

    Lemma logout th g s :
      th ∉ s ->
      used_threads g (s ∪ {[ th ]}) ** locked g th 0 |--
        (|==> used_threads g s ** owned_count_id_frag g None).
    Proof.
      rewrite used_threads.unlock locked.unlock.
      iIntros (Hni) "(? & ? & $)".
      iApply (lock_ghost.logout th g.(locked_gname) s); first done.
      work.
    Qed.

    #[global] Instance owned_count_id_frag_WeaklyObjective γ om :
      WeaklyObjective (PROP := iPropI _) (owned_count_id_frag γ om).
    Proof. rewrite owned_count_id_frag.unlock. apply _. Qed.

    #[global] Instance
      locked_WeaklyObjective γ thr n :
      WeaklyObjective (PROP := iPropI _) (locked γ thr n).
    Proof. rewrite locked.unlock. apply _. Qed.

    Lemma locked_excl_same_thread g th n m :
      locked g th n ** locked g th m |-- False.
    Proof.
      rewrite locked.unlock.
      work.
      iDestruct (not_locked_unique with "[$]") as "[]".
    Qed.

    Lemma locked_excl_different_thread g th th' n m :
      locked g th n ** locked g th' m |-- [| n = 0 \/ m = 0 |] ** True.
    Proof.
      destruct (decide (th = th')) as [->|Hne]. {
        rewrite locked_excl_same_thread. work.
      }
      rewrite locked.unlock.
      iIntros "[[_ A] [_ B]]".
      destruct n, m; try auto. iExFalso.
      rewrite owned_count_id_frag.unlock.
      iDestruct (own_valid_2 with "A B") as %HV; exfalso.
      rewrite -auth_frag_op auth_frag_valid in HV.
      done.
    Qed.

  End locked_with_cpp.

(**
Underlying pthread implementation for [PTHREAD_MUTEX_RECURSIVE_NP] case:

  <<
  /* Check whether we already hold the mutex.  */
  if (mutex->__data.__owner == id)
	{
	  /* Just bump the counter.  */
	  if (__glibc_unlikely (mutex->__data.__count + 1 == 0))
	    /* Overflow of the counter.  */
	    return EAGAIN;

	  ++mutex->__data.__count;

	  return 0;
	}
  (* LLL_MUTEX_LOCK_OPTIMIZED (mutex); *)
  LLL_MUTEX_LOCK (mutex);
  >>

Informally, we can read mutex->__data.__owner atomically, and we know that
mutex->__data.__owner == id if and only if our thread has completed locking the
recursive mutex; hence, mutex->__data.__owner != id means that nobody is
touching the mutex or other threads are operating on it, but at no point will they set __owner to our ID.

Hence:
1. [if (mutex->__data.__owner == id)], we can get obtain sequential ownership of
mutex->__data.__count, and of the underlying resources, and complete the lock operation.
2. else, we can attempt to grab the underlying non-recursive lock, and be sure we
  won't deadlock against ourselves.

Formalizing step 1 seems nontrivial, but relatively routine.
But the full pthread implementation would add annoying details.

The right invariant might resemble the following, but significant details are TBD.
[[
cinv (
  \exists x,
  mutex->__data.__owner |-> x **
  if bool_decide (x <> 0) then
    (sequential ownership of count ** ownership of data protected by the lock) \/
    some exclusive token (* needed to take the sequential out *)
  else
    emp
  )
]]
*)
  (* the mask of recursive_mutex *)
  Definition mask := nroot .@@ "std" .@@ "recursive_mutex" .@@ "mask".

  (** We base the implementation protocol on
  https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/pthread_mutex_lock.c#L90-L112.

  official mirror:
  https://sourceware.org/git/?p=glibc.git;a=blob;f=nptl/pthread_mutex_lock.c;h=a697f2b6ca8dfa9e4557ab3f44b87bc5ceeec014;hb=HEAD#l90
  TODO: revise.
  *)

  (* NOTE: Invariant used to protect resource [r]

      [[
      inv (r \\// exists th n, locked th (S n))
      ]]
   *)


  (** Intended meaning: ownership of physical C++ state for an instance of "std::recursive_mutex". *)
  Parameter rawR : ∀ `{Σ : cpp_logic, σ : genv}, option thread_idT -> nat -> Rep.
  (* The thread_idT is None (0) if there is no owner. *)
  #[only(type_ptr="std::recursive_mutex")] derive rawR.

  Definition rmutex_N : namespace :=
    nroot .@@ "std" .@@ "recursive_mutex" .@ "raw_inv".

  (* recursive mutex -- ownership of the class. *)
  sl.lock
  Definition I `{Σ : cpp_logic, σ : genv, !lockedG Σ} (γ : gname) : Rep :=
    type_ptrR "std::recursive_mutex" **
    cinv rmutex_N γ.(inv_gname) (∃ owner count, rawR owner count **
      (* We use [Nat.pred] because [owned_count_id_auth] stores [counter - 1]. *)
      pureR (owned_count_id_auth γ ((λ t, (t, Nat.pred count)) <$> owner))).
  (* TODO: readd [|owner = None <-> count = O|] elsewhere, as sequential invariant in [R]. *)
  #[only(knowledge,type_ptr="std::recursive_mutex")] derive I.

  sl.lock
  Definition R `{Σ : cpp_logic, σ : genv, !lockedG Σ} (γ : gname) (q : cQp.t) : Rep :=
    type_ptrR "std::recursive_mutex" **
    (* TODO: add here sequential ownership of the lock, and maybe replace I by the lock invariant.
    Something like *)
    (* _mutex_field |-> mutex.R q ... ** *)
    pureR (cinv_own γ.(inv_gname) q).
  #[only(cfractional,ascfractional,timeless,type_ptr="std::recursive_mutex")] derive R.


  Section base_construction.
    Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context `{!lockedG Σ}.

    #[global] Instance I_learn : Cbn (Learn (learn_eq ==> learn_hints.fin) I).
    Proof. solve_learnable. Qed.
    #[global] Instance R_learn : Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    (** <<token γ q>>
        if <<q = 1>>, then the mutex is not locked and therefore can be destroyed.

        <<token γ 1>> is shared among threads who has access to the lock, and a
        call to lock turns some of <<token γ q>> into <<given_token γ q>>, unlock
        does the opposite.
    *)
    Parameter token : gname -> Qp -> mpred.
    #[only(fracsplittable,timeless)] derive token.

    (** Tracks whether any thread holds the lock. *)
    Parameter given_token : gname -> Qp -> mpred.
    #[only(timeless)] derive given_token.
    (* #[only(cfracsplittable,timeless)] derive given_token. *)

    #[global]
    Instance given_token_learn γ : LearnEq1 (given_token γ) :=
      ltac:(solve_learnable).

    cpp.spec "std::recursive_mutex::recursive_mutex()" as ctor_spec with
      (\this this
      \post Exists g, this |-> R g 1$m ** token g 1 ** used_threads g empty).

    cpp.spec "std::recursive_mutex::~recursive_mutex()" as dtor_spec with
      (\this this
      \pre{g} this |-> R g 1$m
      \pre token g 1
      \pre used_threads g empty
      \post emp).

    cpp.spec "std::recursive_mutex::lock()" as lock_spec with
      (\this this
        \prepost{q g} this |-> R g q (* part of both pre and post *)
        \persist{th} current_thread th
        \pre{q'} token g q'
        \pre{Q} AC << ∀ n , locked g th n >> @ top \ ↑ mask , empty
                    << locked g th (S n) , COMM Q >>
        \post Q ** given_token g q').

    cpp.spec "std::recursive_mutex::unlock()" as unlock_spec with
      (\this this
        \prepost{q g} this |-> R g q (* part of both pre and post *)
        \persist{th} current_thread th
        \pre{q'} given_token g q'
        \pre{Q} AC << ∀ n , locked g th (S n) >> @ top \ ↑ mask , empty
                    << locked g th n , COMM Q >>
        \post token g q' ** Q).

  End base_construction.


  (** * Derived construction *)
  Record rmutex_gname :=
    { lock_gname : gname; level_gname : iprop.gname }.
  Definition rmutex_namespace := nroot .@@ "std" .@@ "recursive_mutex" .@@ "derived".

  Canonical Structure cmraR := (excl_authR (prodO natO thread_idTO)).

  sl.lock
  Definition inv_rmutex
      `{Σ : cpp_logic} `{!lockedG Σ} `{!HasOwn (iPropI _) cmraR}
      (g : rmutex_gname) (P : mpred) : mpred :=
    inv rmutex_namespace
      (Exists n th, own g.(level_gname) (●E (n, th)) **
        match n with
        | 0 => P ** own g.(level_gname) (◯E (n, th))
        | S n => locked g.(lock_gname) th (S n)
        end).
  #[only(knowledge)] derive inv_rmutex.

  (** [acquire_state] tracks the acquisition state of a recursive_mutex.
   *)
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

  sl.lock
  Definition acquireable
      `{Σ : cpp_logic, !lockedG Σ, !HasStdThreads Σ, !HasOwn (iPropI _) cmraR}
      (g : rmutex_gname) (th : thread_idT) {TT: tele} (t : acquire_state TT)
      (P : TT -t> mpred) : mpred :=
    current_thread th **
    match t with
    | NotHeld => locked g.(lock_gname) th 0
    | Held n args => own g.(level_gname) (◯E (S n, th)) ** tele_app P args
    end.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Context `{!HasOwn (iPropI _) cmraR, !HasStdThreads Σ}.
    Context `{!lockedG Σ}.

    #[global] Instance acquireable_learn γ th TT : LearnEq2 (acquireable γ th (TT := TT)).
    Proof. solve_learnable. Qed.

    #[global] Instance acquireable_current_thread :
      `{Observe (current_thread th) (acquireable g th (TT := TT) t P)}.
    Proof. rewrite acquireable.unlock; apply _. Qed.

    Lemma use_thread_acquirable {TT} th g m P :
      th ∉ m ->
      current_thread th ** used_threads g.(lock_gname) m |-- (|==>
      used_threads g.(lock_gname) (m ∪ {[ th ]}) ** acquireable (TT := TT) g th NotHeld P).
    Proof.
      rewrite acquireable.unlock /=.
      work.
      wapply use_thread; first done.
      work with br_erefl.
      iModIntro; work.
    Qed.
  End with_cpp.

  Section with_cpp.
    Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context `{!lockedG Σ}.
    Context `{!HasOwn (iPropI _) cmraR}.

    (* Alternative style:
       <<
       R γ q r ** locked γ th (S n) |--| R γ q r ** r ** was_locked γ th (S n)
       >>

       possible solution: two specs/choice in the spec for unlock: either
       <<{locked γ th (n+1)} unlock() {locked γ th n}>>
       or
       <<{was_locked γ th (n+2)} unlock() {locked γ th (n+1)}>>
    *)

    (* TODO make this into a hint *)
    Lemma is_held {TT : tele} {t1 t2 : acquire_state TT} :
      acquire t1 t2 ->
      ∃ n xs, t2 = Held n xs /\
        t1 = release t2.
    Proof.
      rewrite acquire.unlock release.unlock.
      intros.
      destruct t1; simpl in H; eauto.
      - exists 0. naive_solver.
      - exists (S n). naive_solver.
    Qed.

    #[program]
    Definition acquireable_is_acquired_C {TT} g th t t' P
        (_ : acquire (TT := TT) t t') :=
      \cancelx
      \consuming acquireable g th t' P
      \deduce{args} tele_app P args
      \deduce{n} [| t' = Held n args /\ t = release t' |]
      \deduce own g.(level_gname) (◯E (S n, th))
      \end.
    Next Obligation.
      intros * (? & ? & -> & ->)%is_held.
      rewrite acquireable.unlock.
      ego.
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
    Next Obligation. rewrite acquireable.unlock; work. Qed.

    #[program]
    Definition own_P_is_acquireable_C {TT} g n P :=
      \cancelx
      \preserving{th} current_thread th
      \consuming own g.(level_gname) (◯E (S n, th))
      \bound n' args
      \proving acquireable (TT := TT) g th (Held n' args) P
      \through tele_app P args
      \through [| n' = n |]
      \end.
    Next Obligation. rewrite acquireable.unlock; work. Qed.

    #[global] Instance : `{Learnable
      (current_thread th)
      (acquireable (TT := TT0) γ th0 args P0)
      [th0 = th] }.
    Proof. solve_learnable. Qed.

    #[global] Instance learn_inv_rmutex_γ : `{Learnable
      (inv_rmutex γ1 P1)
      (inv_rmutex γ2 P2)
      [γ2 = γ1] }.
    Proof. solve_learnable. Qed.

    #[global] Instance learn_inv_rmutex_TT : `{Learnable
      (inv_rmutex γ (∃ xs : tele_arg TT1, tele_app P1 xs))
      (inv_rmutex γ (∃ xs : tele_arg TT2, tele_app P2 xs))
      [TT2 = TT1] }.
    Proof. solve_learnable. Qed.

    #[global] Instance learn_inv_rmutex_P TT : `{Learnable
      (inv_rmutex γ1 (∃ xs : tele_arg TT, tele_app P1 xs))
      (inv_rmutex γ2 (∃ xs : tele_arg TT, tele_app P2 xs))
      [P2 = P1] }.
    Proof. solve_learnable. Qed.

    #[global] Instance learn_args
      {TT: tele} (t : acquire_state TT) (P : TT -t> mpred) :
      `{Learnable
      (tele_app P args ** own (level_gname γ) (◯E (S n, th)))
      (acquireable γ th t P)
      [t = Held n args] }.
    Proof. solve_learnable. Qed.

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

    (* this is the usable pre-condition *)
    cpp.spec "std::recursive_mutex::recursive_mutex()" as ctor_spec' with
      (\this this
      \persist{th} current_thread th
      \pre{TT P xs} |> tele_app (TT := TT) P xs
      \require ∀ xs, WeaklyObjective (tele_app P xs)
      \post
        Exists g,
          this |-> R g.(lock_gname) 1$m **
          token g.(lock_gname) 1 **
          used_threads g.(lock_gname) empty **
          inv_rmutex g (∃ xs, tele_app P xs)).

    cpp.spec "std::recursive_mutex::~recursive_mutex()" as dtor_spec' with
      (\this this
      \pre{g} this |-> R g.(lock_gname) 1
      \pre token g.(lock_gname) 1
      \pre used_threads g.(lock_gname) empty
      \pre{TT P} inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
      \post |> (Exists xs, tele_app (TT := TT) P xs)).

    cpp.spec "std::recursive_mutex::lock()" as lock_spec' with
      (\this this
      \persist{g TT P} inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
      \prepost{q} this |-> R g.(lock_gname) q
      \pre{th n} acquireable g th n P
      \pre{q'} token g.(lock_gname) q'
      \post given_token g.(lock_gname) q' ** (Exists n', [| acquire n n' |] ** ▷ acquireable g th n' P)).
    (* to prove: this is derivable from lock_spec *)

    cpp.spec "std::recursive_mutex::unlock()" as unlock_spec' with
      (\this this
      \persist{g TT P} inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
      \prepost{q} this |-> R g.(lock_gname) q
      \pre{th n args} acquireable g th (Held n args) P
      \pre{q'} given_token g.(lock_gname) q'
      \post token g.(lock_gname) q' ** acquireable g th (release $ Held n args) P).

    Definition do_lock g K : mpred := ∃ TT P th n q',
      inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
      ** acquireable g th n P
      ** token g.(lock_gname) q'
      ** (
        (* TODO readd *)
        (* ▷ *)
        (given_token g.(lock_gname) q' **
        (Exists n', [| acquire n n' |] ** ▷ acquireable g th n' P)) -*
        K).
    #[global] Arguments do_lock /.

    Definition do_unlock g K : mpred := ∃ TT P th n args q',
      inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
      ** acquireable g th (Held n args) P
      ** given_token g.(lock_gname) q'
      ** (
        (* TODO readd *)
        (* ▷ *)
        (token g.(lock_gname) q' ** acquireable g th (release $ Held n args) P) -*
        (|={⊤}=> K)).
    #[global] Arguments do_unlock /.

    #[global] Instance recursive_mutex_basic_lockable : BasicLockable (T:=rmutex_gname) "std::recursive_mutex" (λ q γ, R γ.(lock_gname) q) :=
    { do_lock := fun this => do_lock
    ; do_unlock := fun this => do_unlock }.

    cpp.spec "std::recursive_mutex::lock()" as lock_spec_alt' with
    (\exact Reduce (lock_basic_lockable "std::recursive_mutex" (λ q γ, R γ.(lock_gname) q))).

    cpp.spec "std::recursive_mutex::unlock()" as unlock_spec_alt' with
    (\exact Reduce (unlock_basic_lockable "std::recursive_mutex" (λ q γ, R γ.(lock_gname) q))).

    Lemma lock_spec'_equiv_lock_spec_alt' :
      lock_spec' -|- lock_spec_alt'.
    Proof. iSplit; iApply specify_mono; ework with br_erefl. Qed.

    Lemma unlock_spec'_equiv_unlock_spec_alt' :
      unlock_spec' -|- unlock_spec_alt'.
    Proof.
    iSplit; iApply specify_mono_fupd; work; iModIntro.
      2: {
        ework with br_erefl.
        iSplitL; iIntros "? !>"; work.
      }
      ework with br_erefl.
      iModIntro; work.
    Qed.

    Definition acquireable_current_thread_F :=
      ltac:(mk_obs_fwd acquireable_current_thread).
    #[local] Hint Resolve acquireable_current_thread_F : br_hints.

    (* TODO AUTO *)
    #[global] Instance later_acquireable_learn γ th TT :
      LearnEq2 (fun a b => bi_later (acquireable γ th (TT := TT) a b)).
    Proof. solve_learnable. Qed.

    Import linearity.

    Context `{HOV : !HasOwnValid mpredI cmraR, HOU : !HasOwnUpd mpredI cmraR}.

    Lemma ctor_spec_impl_ctor_spec' :
      ctor_spec |-- ctor_spec'.
    Proof using MOD HOV HOU.
      apply specify_mono_fupd; work.
      iModIntro; work.
      rewrite /acquireable /=.
      iMod (own_alloc (●E (O, th) ⋅ ◯E (O, th))) as (g) "(? & ?)".
      { apply excl_auth_valid. }
      iExists {| lock_gname := t; level_gname := g |}; iFrame.
      rewrite inv_rmutex.unlock.
      iMod (inv_alloc with "[-]") as "$"; last done.
      ework with br_erefl.
    Qed.

    Lemma dtor_spec_impl_dtor_spec' :
      dtor_spec |-- dtor_spec'.
    Proof using MOD HOV HOU.
      apply specify_mono_fupd; work.
      rewrite inv_rmutex.unlock.
      iInv recursive_mutex.rmutex_namespace as (n th) "[>? ?]" "Hclose".
      (* TODO: we should cancel this invariant instead *)
      (* iMod (cinv_cancel with "[$]") as "?". *)

      destruct n as [|n'] eqn:?; work; first last.
      {
        rewrite locked.unlock used_threads.unlock.
        work.
        iDestruct (used_threads_empty_no_not_locked with "[$]") as "[]".
        (* Somebody else has locked the mutex, but we have the full token.
        This should be impossible, since we own [token 1], but it's unclear how we'd prove this. *)
      }
      iMod ("Hclose" with "[]") as "_". {
        (* We should _cancel_ the invariant, then we would _not_ need to prove this. *)
        admit.
      }
      iModIntro. work.
      iModIntro.
      ego with br_erefl.
      wname [inv] "I".
      wname [own] "L1".
      wname [own] "L2".
      iCombine "L1 L2" as "L".
      (* _now_ we just need to leak ghost state and that's okay *)
      iApply (affine with "L").
      apply mpred_BiAffine.
      Unshelve.
      all: fail.
    (* Abort this until we have a cancellable invariant. *)
    Abort.

    Lemma lock_spec_impl_lock_spec' :
      lock_spec |-- lock_spec'.
    Proof using MOD HOV HOU.
      apply specify_mono; work.
      Import auto_frac.
      iExists q, q'.

      iExists (∃ t, [| acquire n t |] ∗ ▷ acquireable g th t P)%I.

      wname [bi_wand] "W".
      wfocus (bi_wand _ _) "W".
      { work $usenamed=true. }
      work.
      iAcIntro; rewrite /commit_acc/=.
      rewrite inv_rmutex.unlock acquireable.unlock.
      iInv rmutex_namespace as (??) "(>Hn & Hcases)" "Hclose".
      work.
      destruct n; simpl.
      - iApply fupd_mask_intro; first set_solver; iIntros "Hclose'".
        work.
        iExists 0; work.
        destruct n0; first last. {
          iMod "Hcases".
          iDestruct (locked_excl_different_thread with "[$]") as (?) "?".
          exfalso. lia.
        }
        iDestruct "Hcases" as "(HP & >Hcase)".
        iMod (own_update_2 with "Hn Hcase") as "(Hg & Hcase)";
          first apply (excl_auth_update _ _ (1, th)).
        iMod "Hclose'" as "_".
        wname [recursive_mutex.locked _ th _] "Hlocked".
        iMod ("Hclose" with "[$Hg $Hlocked //]") as "_".
        iMod (bi.later_exist_except_0 with "HP") as "(%args & HP)".
        iModIntro.
        iExists (Held 0 args); work $usenamed=true.
      - work.
        iDestruct (own_valid_2 with "Hn [$]") as %[=]%excl_auth_agree_L; subst.
        iMod "Hcases".
        iApply fupd_mask_intro; first set_solver; iIntros "Hclose'".
        iExists (S n). work $usenamed=true.
        iMod (own_update_2 with "Hn [$]") as "(Hg & Hcase)";
          first apply (excl_auth_update _ _ (S (S n), th)).
        iMod "Hclose'" as "_".
        wname [recursive_mutex.locked _ th _] "Hlocked".
        iMod ("Hclose" with "[$Hg $Hlocked //]") as "_".
        iModIntro.
        iExists (Held (S n) xs). work $usenamed=true.
    Qed.

    Lemma unlock_spec_impl_unlock_spec' :
      unlock_spec |-- unlock_spec'.
    Proof using MOD HOV HOU.
      apply specify_mono; work.
      iExists _, (acquireable g th (release $ Held n args) P)%I.
      work.
      iAcIntro; rewrite /commit_acc/=.
      rewrite inv_rmutex.unlock acquireable.unlock.
      iInv rmutex_namespace as (??) "(>Hn & Hcases)" "Hclose".
      work.
      iDestruct (own_valid_2 with "Hn [$]") as %[=]%excl_auth_agree_L; subst.
      iMod "Hcases".
      iApply fupd_mask_intro; first set_solver; iIntros "Hclose'".
      ework $usenamed=true with br_erefl.
      iMod "Hclose'" as "_".
      iMod (own_update_2 with "Hn [$]") as "(Hg & Hcase)";
        first apply (excl_auth_update _ _ (n, th)).
      iFrame "#".
      rewrite release.unlock.
      destruct n; iFrame.
      all: iMod ("Hclose" with "[-]") as "_";
        ework $usenamed=true with br_erefl; done.
    Qed.

  End with_cpp.

  #[global] Hint Resolve acquireable_acquireable_C : br_hints.
  #[global] Hint Resolve acquireable_is_acquired_C : br_hints.
  #[global] Hint Resolve own_P_is_acquireable_C : br_hints.
  #[global] Hint Resolve acquireable_current_thread_F : br_hints.

End recursive_mutex.
