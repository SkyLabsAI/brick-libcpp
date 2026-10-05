Require Import iris.algebra.gset.
Require Import iris.algebra.coPset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.

Import linearity.

(** This file contains: 
      - Atomic specs for recursive mutex [RecursiveMutexAtomicSpecs].
      - An instantiation of (non-atomic) recursive mutex predicates
        (which can be plugged into [recursive_mutex_spec]).
      - A proof that the non-atomic specs refine the atomic version.
*)

(** Atomic specs for recursive mutex. *)
Module RecursiveMutexAtomicSpecs (T : MutexCPPName).
  (* FIXME the hardcoded strings can be derived from T.cpp_ty. *)

  (* Not prodO thread_idTO natO. *)
  (* [locked γ qt th 0] does not identify the thread holding the mutex. *)
  Canonical Structure phys_stateUR := authR (optionR (exclR (prodO thread_idTO natO))).

  (** [locked γ qt th n] records [n] acquisitions by [th], using token share [qt]. *)
  Class lockedG `{Σ : cpp_logic} := {
    #[global] sets_G :: MutexSets.G Σ;
    #[global] tokens_G :: MutexTokens.G Σ;

    #[local] has_phys_state :: HasOwn (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_upd :: HasOwnUpd (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_valid :: HasOwnValid (iPropI _Σ) phys_stateUR;
    #[local] has_phys_state_unit :: HasOwnUnit mpredI phys_stateUR;
  }.
  #[global] Arguments lockedG {_ _} Σ : assert.

  Record gname : Set := MkGname
  { owned_count_id : iprop.gname;
    pool_name : iprop.gname;
    mutex_inv_namespace : namespace;
    inv_gname : iprop.gname;
    token_gname : iprop.gname;
  }.

  Definition token `{Σ : cpp_logic, !lockedG Σ} (g : gname) (qt : cQp.t) : mpred :=
    MutexTokens.token g.(token_gname) qt.
  Definition given_token `{Σ : cpp_logic, !lockedG Σ} (g : gname) (qt : cQp.t) : mpred :=
    MutexTokens.given_token g.(token_gname) qt.
  #[global] Instance token_timeless `{Σ : cpp_logic, !lockedG Σ} g qt :
    Timeless (token g qt).
  Proof. rewrite /token. apply _. Qed.
  #[global] Instance token_WeaklyObjective `{Σ : cpp_logic, !lockedG Σ} g qt :
    WeaklyObjective (token g qt).
  Proof. rewrite /token /MutexTokens.token. apply _. Qed.
  #[global] Instance given_token_timeless `{Σ : cpp_logic, !lockedG Σ} g qt :
    Timeless (given_token g qt).
  Proof. rewrite /given_token. apply _. Qed.
  #[global] Instance given_token_WeaklyObjective `{Σ : cpp_logic, !lockedG Σ} g qt :
    WeaklyObjective (given_token g qt).
  Proof. rewrite /given_token /MutexTokens.given_token. apply _. Qed.
  #[global] Hint Opaque token given_token : sl_opacity typeclass_instances.

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

  (** For positive [n], [locked γ qt th n] records the physical lock count
      through [owned_count_id_frag]. At zero it owns the namespace permission
      and registration token. The first lock transfers that permission into
      the physical invariant; the final unlock returns it. *)
  sl.lock
  Definition locked `{Σ : cpp_logic, !lockedG Σ}
      (γ : gname) (qt : cQp.t) (th : thread_idT) (n : nat) : mpred :=
    match n with
    | 0 => MutexSets.my_mutexes γ.(pool_name) th
        (CoPset $ ↑γ.(mutex_inv_namespace)) ** token γ qt
    | S n => owned_count_id_frag γ (Some (th, n)) ** given_token γ qt
    end.
  #[only(timeless)] derive locked.

  Section locked_with_cpp.
    Context `{Σ : cpp_logic}.
    Context `{!lockedG Σ}.
    Context `{!HasStdThreads Σ}.

    #[global] Instance owned_count_id_frag_WeaklyObjective γ om :
      WeaklyObjective (PROP := iPropI _) (owned_count_id_frag γ om).
    Proof. rewrite owned_count_id_frag.unlock. apply _. Qed.

    #[global] Instance
      locked_WeaklyObjective γ qt thr n :
      WeaklyObjective (PROP := iPropI _) (locked γ qt thr n).
    Proof. rewrite locked.unlock. apply _. Qed.

    Lemma locked_excl_different_thread g qt qt' th th' n m :
      locked g qt th n ** locked g qt' th' m |-- [| n = 0 \/ m = 0 |] ** True.
    Proof.
      rewrite locked.unlock.
      iIntros "[H1 H2]".
      destruct n, m; try auto. iExFalso.
      iDestruct "H1" as "[A _]". iDestruct "H2" as "[B _]".
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
1. [if (mutex->__data.__owner == id)], we can get sequential ownership of
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
      inv (r \\// exists qt th n, locked qt th (S n))
      ]]
   *)


  (** Intended meaning: ownership of physical C++ state for an instance of "std::recursive_mutex". *)
  Parameter rawR : ∀ `{Σ : cpp_logic, σ : genv}, option thread_idT -> nat -> Rep.
  (* The thread_idT is None (0) if there is no owner. *)
  Axiom rawR_type_ptr : ∀ `{Σ : cpp_logic, σ : genv} o n,
    Observe (type_ptrR T.cpp_ty) (rawR o n).
  #[global] Existing Instance rawR_type_ptr.

  Definition rmutex_N : namespace :=
    nroot .@@ "std" .@@ "recursive_mutex" .@ "raw_inv".

  sl.lock
  Definition R `{Σ : cpp_logic, σ : genv, !lockedG Σ} (γ : gname) (q : cQp.t) : Rep :=
    type_ptrR T.cpp_ty **
    as_Rep (fun this => cinv rmutex_N γ.(inv_gname)
      (∃ owner count, this |-> rawR owner count **
        (* [owned_count_id_auth] stores [counter - 1]. *)
        owned_count_id_auth γ ((λ t, (t, Nat.pred count)) <$> owner) **
        match owner with
        | None => MutexTokens.token_full γ.(token_gname)
        | Some th => MutexTokens.token_not_full γ.(token_gname) **
            MutexSets.my_mutexes γ.(pool_name) th
              (CoPset $ ↑γ.(mutex_inv_namespace))
        end)) **
    pureR (cinv_own γ.(inv_gname) q).
  (* TODO: add sequential ownership of the physical lock and
     [|owner = None <-> count = O|]. *)
  #[only(cfractional,cfracvalid,ascfractional)] derive R.
  #[global] Instance R_type_ptr `{Σ : cpp_logic, σ : genv, !lockedG Σ} γ q :
    Observe (type_ptrR T.cpp_ty) (R γ q).
  Proof. rewrite R.unlock. apply _. Qed.


  Section base_construction.
    Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context `{!lockedG Σ}.

    #[global] Instance R_learn : Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    Definition ctor_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
      \pre{pool N} emp
      \post Exists g,
        [| pool_name g = pool /\ mutex_inv_namespace g = N |] **
        this |-> R g 1$m ** token g 1$m).

    Definition dtor_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
      \pre{g} this |-> R g 1$m
      \pre token g 1$m
      \post emp).

    Definition lock_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
        \prepost{q g} this |-> R g q (* part of both pre and post *)
        \persist{th} current_thread th
        \pre{qt Q} AC << ∀ n , locked g qt th n >> @ top \ ↑ mask , empty
                    << locked g qt th (S n), COMM Q >>
        \post Q).

    Definition unlock_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
        \prepost{q g} this |-> R g q (* part of both pre and post *)
        \persist{th} current_thread th
        \pre{qt Q} AC << ∀ n , locked g qt th (S n) >> @ top \ ↑ mask , empty
                    << locked g qt th n, COMM Q >>
        \post Q).

    Lemma locked_contradict_full_token (this : ptr) g q qt th n {E : coPset} :
      ↑rmutex_N ⊆ E ->
      this |-> R g q ** token g 1$m ** locked g qt th (S n) |--
      (|={E}=> False).
    Proof.
      intros HE.
      rewrite R.unlock locked.unlock /token !_at_sep
        !_at_pureR _at_as_Rep.
      iIntros "((_ & #HI & Hown) & Htoken & Hcount & _)".
      iInv rmutex_N as "[(%owner & %count & _ & >Hauth & Hbalance) Hown]".
      destruct owner as [owner|].
      - iDestruct "Hbalance" as "[Hbalance _]".
        iAssert (▷ False)%I with "[Hbalance Htoken]" as "Hfalse".
        { iNext. iApply MutexTokens.token_not_full_full_token. iFrame. }
        iMod "Hfalse" as %[].
      - iEval (rewrite owned_count_id_auth.unlock /=) in "Hauth".
        iEval (rewrite owned_count_id_frag.unlock) in "Hcount".
        iDestruct (own_valid_2 with "Hauth Hcount") as %Hvalid.
        exfalso. move: Hvalid. rewrite auth_both_valid_discrete /=.
        rewrite option_included. naive_solver.
    Qed.

  End base_construction.
End RecursiveMutexAtomicSpecs.

(** An instantiation of RecursiveMutexPreds. This is built on top of predicates
    in RecursiveMutexAtomicSpecs, so the abstraction here is not ideal.
    The main result here is that the atomic specs can derive the non-atomic 
    ones; see the [RecursiveMutexRefinement] module defined later. *)
Module RecursiveMutexPreds (T : MutexCPPName) <: RECURSIVE_MUTEX_PREDS T.
  Module at_specs := RecursiveMutexAtomicSpecs T.
  Include RecursiveMutexState.

  Definition cpp_ty : type := T.cpp_ty.
  #[global] Hint Opaque cpp_ty : sl_opacity.

  Record rmutex_gname := MkGname
    { lock_gname : at_specs.gname
    ; level_gname : iprop.gname
    ; cinv_gname : iprop.gname
    }.
  Definition gname := rmutex_gname.
  Definition pool_name (g : gname) := at_specs.pool_name g.(lock_gname).
  Definition rmutex_inv_namespace (g : gname) :=
    at_specs.mutex_inv_namespace g.(lock_gname).

  (** Remember the acquired share as well as the count and owner, so the
      final unlock returns the same share that was registered. *)
  Canonical Structure cmraR :=
    excl_authR (prodO (prodO natO thread_idTO) (leibnizO cQp.t)).

  Class recursive_mutexG `{Σ : cpp_logic} := {
    #[global] locked_G :: at_specs.lockedG Σ;
    #[global] level_own :: HasOwn (iPropI _Σ) cmraR;
    #[global] level_valid :: HasOwnValid (iPropI _Σ) cmraR;
  }.
  Definition G := @recursive_mutexG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance recursive_mutex_G `{Σ : cpp_logic} (H : G Σ) :
    @recursive_mutexG _ _ Σ := H.

  #[global] Instance sets_G `{Σ : cpp_logic, !G Σ} : MutexSets.G Σ := _.

  Definition rmutex_namespace :=
    nroot .@@ "std" .@@ "recursive_mutex" .@@ "derived".

  sl.lock
  Definition inv_rmutex `{Σ : cpp_logic, !G Σ}
      (g : gname) (P : mpred) : mpred :=
    cinv rmutex_namespace g.(cinv_gname)
      (Exists n th qt, own g.(level_gname) (●E (n, th, qt)) **
        match n with
        | 0 => P ** own g.(level_gname) (◯E (n, th, qt))
        | S n => at_specs.locked g.(lock_gname) qt th (S n)
        end).
  #[only(knowledge)] derive inv_rmutex.

  (** Fractional ownership of the physical mutex, its invariant lifetime,
      and the protected resource protocol. *)
  Definition R `{Σ : cpp_logic, !G Σ} {HAS_THREADS : HasStdThreads Σ}
      {σ : genv} (g : gname) (q : cQp.t) (P : mpred) : Rep :=
    at_specs.R g.(lock_gname) q **
    pureR (cinv_own g.(cinv_gname) q) ** pureR (inv_rmutex g P).
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(cfractional,cfracvalid,ascfractional)] derive R.
  #[global] Instance R_type_ptr `{Σ : cpp_logic, !G Σ}
      {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P :
    Observe (type_ptrR cpp_ty) (R g q P).
  Proof. rewrite /R. apply _. Qed.

  Definition token `{Σ : cpp_logic, !G Σ} (g : gname) (qt : cQp.t) : mpred :=
    at_specs.token g.(lock_gname) qt.
  #[global] Instance token_fractional `{Σ : cpp_logic, !G Σ} g :
    CFractional (token g).
  Proof. intros q1 q2. rewrite /token /at_specs.token cQp.frac_add. apply MutexTokens.token_fractional. Qed.
  #[global] Instance token_timeless `{Σ : cpp_logic, !G Σ} g qt : Timeless (token g qt).
  Proof. rewrite /token /at_specs.token. apply _. Qed.
  #[global] Hint Opaque token : sl_opacity typeclass_instances.

  Definition given_token `{Σ : cpp_logic, !G Σ}
      (g : gname) (qt : cQp.t) (th : thread_idT) (n : nat) : mpred :=
    own g.(level_gname) (◯E (S n, th, qt)).
  #[global] Hint Opaque given_token : sl_opacity typeclass_instances.
  #[global] Instance given_token_timeless `{Σ : cpp_logic, !G Σ} g qt th n :
    Timeless (given_token g qt th n).
  Proof. rewrite /given_token. apply _. Qed.

  Definition not_locked `{Σ : cpp_logic, !G Σ}
      (g : gname) (th : thread_idT) (E : coPset_disj) : mpred :=
    MutexSets.my_mutexes (pool_name g) th E.
  Definition locked `{Σ : cpp_logic, !G Σ, σ : genv}
      (_this : ptr) (g : gname) (qt : cQp.t) (th : thread_idT) (n : nat) : mpred :=
    given_token g qt th n.
  #[global] Instance not_locked_timeless `{Σ : cpp_logic, !G Σ} g th E :
    Timeless (not_locked g th E).
  Proof. rewrite /not_locked. apply _. Qed.
  #[global] Instance locked_timeless `{Σ : cpp_logic, !G Σ, σ : genv} this g qt th n :
    Timeless (locked this g qt th n).
  Proof. rewrite /locked. apply _. Qed.
  #[global] Hint Opaque not_locked locked : sl_opacity typeclass_instances.

  Section rules.
    Context `{Σ : cpp_logic, !G Σ}.

    Lemma register_thread g th :
      MutexSets.my_mutexes (pool_name g) th (CoPset $ ↑rmutex_inv_namespace g) ⊣⊢
      not_locked g th (CoPset $ ↑rmutex_inv_namespace g).
    Proof. by rewrite /not_locked. Qed.

    Context `{!HasStdThreads Σ} {σ : genv}.

    Lemma locked_contradict_full_token (this : ptr) g q qt th n P :
      this |-> R g q P ** token g 1$m ** locked this g qt th n |--
      (|={⊤}=> False).
    Proof.
      rewrite /R /token /locked /given_token !_at_sep !_at_pureR inv_rmutex.unlock.
      iIntros "((HR & Hown & #Hinv) & Htoken & Hheld)".
      iInv rmutex_namespace as "[(%n' & %th' & %qt' & >Hauth & Hcase) Hown]".
      iDestruct (own_valid_2 with "Hauth Hheld") as %[=]%excl_auth_agree_L; subst.
      iMod "Hcase" as "Hlocked".
      iMod (at_specs.locked_contradict_full_token with "[$HR $Htoken $Hlocked]") as %[].
      have Hdisjoint : (↑at_specs.rmutex_N : coPset) ## ↑rmutex_namespace.
      {
        rewrite /at_specs.rmutex_N /rmutex_namespace.
        set base := nroot .@@ "std" .@@ "recursive_mutex".
        have Hraw : base .@ "raw_inv" = base .@ (encode "raw_inv").
        { by rewrite !namespaces.ndot_unseal. }
        have Hderived : base .@@ "derived" = base .@ (encode "derived"%bs).
        { by rewrite !namespaces.ndot_unseal. }
        rewrite Hraw Hderived. apply ndot_ne_disjoint. vm_compute. discriminate.
      }
      set_solver.
    Qed.

  End rules.
End RecursiveMutexPreds.

(** Atomic specs derive the non-atomic specs. *)
Module RecursiveMutexRefinement (T : MutexCPPName).
  Module Preds := RecursiveMutexPreds T.
  Import Preds.
  Module Spec := recursive_mutex_spec T Preds.
  Import Spec (acquireable).

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!G Σ}.
  Context `{HOV : !HasOwnValid mpredI cmraR, HOU : !HasOwnUpd mpredI cmraR}.

  (* basically std_ctor_atomic_spec |-- std_ctor_non_atomic_spec *)
  Lemma at_spec_impl_na_spec_ctor this :
    elaborate.spec_entails_fupd
      (Preds.at_specs.ctor_spec_body this)
      (Spec.ctor_spec this).
  Proof using MOD HOV HOU.
    work.
    iModIntro; work.
    iExists pool, N. work.
    rewrite /acquireable /=.
    (* The owner slot is unused while the initial count is zero. *)
    set th : thread_idT := inhabitant.
    iMod (own_alloc (●E (O, th, (1$m)%cQp) ⋅ ◯E (O, th, (1$m)%cQp))) as (g) "(? & ?)".
    { apply excl_auth_valid. }
    wname [_ |-> _ _ _] "a".
    wname [at_specs.token] "Htoken".
    iMod (cinv_alloc with "[-a Htoken]") as (ginv) "(#Hinv & Hown)"; last first.
    - iExists {| lock_gname := t; level_gname := g; cinv_gname:= ginv |}.
      rewrite /R /token /pool_name /rmutex_inv_namespace !_at_sep !_at_pureR inv_rmutex.unlock /=.
      iModIntro.
      go with br_erefl $usenamed=true.
    - ework with br_erefl.
    - apply _.
  Qed.

  Lemma at_spec_impl_na_spec_dtor this :
    elaborate.spec_entails_fupd
      (Preds.at_specs.dtor_spec_body this)
      (Spec.dtor_spec this).
  Proof using MOD HOV HOU.
    work.
    rewrite /R /token /pool_name /rmutex_inv_namespace !_at_sep !_at_pureR inv_rmutex.unlock.
    work.
    iMod (cinv_cancel with "[$] [$]") as (n th qt) "(>? & ?)"; [done..|].

    destruct n as [|n'] eqn:?; work; first last.
    {
      iMod (at_specs.locked_contradict_full_token with "[$]") as %[]; first set_solver.
    }
    iModIntro. work. iModIntro. ego with br_erefl.
    (* _now_ we just need to leak ghost state and that's okay *)
    iDestruct select (own _ (●E _)) as "L1".
    iDestruct select (own _ (◯E _)) as "L2".
    iCombine "L1 L2" as "L".
    iApply (affine with "L"). apply mpred_BiAffine.
  Qed.

  Lemma at_spec_impl_na_spec_lock this (xs : list val) (K : val -> mpred) :
    Spec.lock_spec this xs K
    |-- Preds.at_specs.lock_spec_body this xs K.
  Proof using MOD HOV HOU.
    revert xs K.
    change (elaborate.spec_entails
      (Preds.at_specs.lock_spec_body this)
      (Spec.lock_spec this)).
    work.
    rewrite /R !_at_sep !_at_pureR; work.
    iExists q, qt, (cinv_own g.(cinv_gname) q **
      (∃ t, [| acquire n t |] ∗ ▷ acquireable this g qt th t P))%I.
    wname [bi_wand] "W"; wfocus (bi_wand _ _) "W". { work $usenamed=true. }
    rewrite inv_rmutex.unlock /acquireable /not_locked /locked /given_token
      /token /pool_name /rmutex_inv_namespace.
    work; iAcIntro; rewrite /commit_acc/=; work.
    iInv rmutex_namespace as "[(%n' & %th' & %qt' & >Hn & Hcases) ?]" "Hclose".
    destruct n as [|n args]; simpl; [iExists 0 | iExists (S n)].
    1: rewrite [in at_specs.locked _ _ _ 0]at_specs.locked.unlock /=.
    all: work.
    2: iDestruct (own_valid_2 with "Hn [$]") as %[=]%excl_auth_agree_L; subst.
    all: work $usenamed=true; iApply fupd_mask_intro; first set_solver;
      iIntros "Hclose'"; work; iMod "Hclose'" as "_".
    - destruct n'; first last. {
        iMod "Hcases".
        iDestruct (Preds.at_specs.locked_excl_different_thread with "[$]") as (?) "?".
        exfalso. lia.
      }
      rewrite bi.later_sep bi.later_exist_except_0.
      iDestruct "Hcases" as "(>(%args & ?) & >Hcase)".
      iMod (own_update_2 with "Hn Hcase") as "(Hg & ?)";
        first apply (excl_auth_update _ _ (1, th, qt)).
      wname [Preds.at_specs.locked _ qt th _] "Hlocked";
        iMod ("Hclose" with "[$Hg $Hlocked //]") as "_"; iModIntro.
      iExists (Held 0 args). rewrite /acquireable /locked /given_token /=. work.
    - iMod (own_update_2 with "Hn [$]") as "(Hg & ?)";
        first apply (excl_auth_update _ _ (S (S n), th, qt)).
      wname [Preds.at_specs.locked _ qt th _] "Hlocked";
        iMod ("Hclose" with "[$Hg $Hlocked //]") as "_"; iModIntro.
      iExists (Held (S n) args). rewrite /acquireable /locked /given_token /=. work.
  Qed.

  Lemma at_spec_impl_na_spec_unlock this (xs : list val) (K : val -> mpred) :
    Spec.unlock_spec this xs K
    |-- Preds.at_specs.unlock_spec_body this xs K.
  Proof using MOD HOV HOU.
    revert xs K.
    change (elaborate.spec_entails
      (Preds.at_specs.unlock_spec_body this)
      (Spec.unlock_spec this)).
    work.
    rewrite /R !_at_sep !_at_pureR; work.
    iExists q, qt, (cinv_own g.(cinv_gname) q **
      acquireable this g qt th (release $ Held n args) P)%I.
    wname [bi_wand] "W"; wfocus (bi_wand _ _) "W". { work $usenamed=true. }
    rewrite inv_rmutex.unlock /acquireable /not_locked /locked /given_token
      /token /pool_name /rmutex_inv_namespace.
    work; iAcIntro; rewrite /commit_acc/=; work.
    iInv rmutex_namespace as "[(%n' & %th' & %qt' & >Hn & Hcases) ?]" "Hclose".
    iDestruct (own_valid_2 with "Hn [$]") as %[=]%excl_auth_agree_L; subst.
    iMod "Hcases".
    iApply fupd_mask_intro; first set_solver; iIntros "Hclose'".
    iExists n; work $usenamed=true.
    iMod "Hclose'" as "_".
    iMod (own_update_2 with "Hn [$]") as "(Hg & Hcase)";
      first apply (excl_auth_update _ _ (n, th, qt)).
    rewrite /acquireable /not_locked /locked /given_token /token
      /pool_name /rmutex_inv_namespace release.unlock; destruct n.
    1: rewrite [in at_specs.locked _ _ _ 0]at_specs.locked.unlock /=.
    1: iDestruct select (MutexSets.my_mutexes _ _ _ ** at_specs.token _ _) as "[? ?]".
    all: iFrame "#∗".
    all: iMod ("Hclose" with "[-]") as "_";
      ework $usenamed=true with br_erefl; done.
  Qed.

End with_cpp.
End RecursiveMutexRefinement.
