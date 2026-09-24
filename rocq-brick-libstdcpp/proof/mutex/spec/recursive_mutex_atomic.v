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
  (* at_specs thread that has zero, locked γ th 0 does not even know which thread has non-0. *)
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
    user γ.(locked_gname) th **
    match n with
    | 0 => owned_count_id_frag γ None
    | S n => owned_count_id_frag γ (Some (th, n))
    end.
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
      rewrite used_threads.unlock locked.unlock owned_count_id_frag.unlock /=.
      iIntros (Hni) "at_specs".
      iMod (lock_ghost.login with "at_specs") as "[$ $]"; first done.
      iApply own_unit.
    Qed.

    Lemma logout th g s :
      th ∉ s ->
      used_threads g (s ∪ {[ th ]}) ** locked g th 0 |--
        (|==> used_threads g s ** owned_count_id_frag g None).
    Proof.
      rewrite used_threads.unlock locked.unlock.
      iIntros (Hni) "(? & ? & $)".
      iApply lock_ghost.logout; first done.
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
      iDestruct (user_unique with "[$]") as "[]".
    Qed.

    Lemma locked_excl_different_thread g th th' n m :
      locked g th n ** locked g th' m |-- [| n = 0 \/ m = 0 |] ** True.
    Proof.
      destruct (decide (th = th')) as [->|Hne]. {
        rewrite locked_excl_same_thread. work.
      }
      rewrite locked.unlock.
      iIntros "[[_ at_specs] [_ B]]".
      destruct n, m; try auto. iExFalso.
      rewrite owned_count_id_frag.unlock.
      iDestruct (own_valid_2 with "at_specs B") as %HV; exfalso.
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
      inv (r \\// exists th n, locked th (S n))
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

  (* recursive mutex -- ownership of the class. *)
  sl.lock
  Definition I `{Σ : cpp_logic, σ : genv, !lockedG Σ} (γ : gname) : Rep :=
    type_ptrR T.cpp_ty **
    cinv rmutex_N γ.(inv_gname) (∃ owner count, rawR owner count **
      (* We use [Nat.pred] because [owned_count_id_auth] stores [counter - 1]. *)
      pureR (owned_count_id_auth γ ((λ t, (t, Nat.pred count)) <$> owner))).
  (* TODO: readd [|owner = None <-> count = O|] elsewhere, as sequential invariant in [R]. *)
  #[only(knowledge (*,type_ptr="std::recursive_mutex"*) )] derive I.

  sl.lock
  Definition R `{Σ : cpp_logic, σ : genv, !lockedG Σ} (γ : gname) (q : cQp.t) : Rep :=
    type_ptrR T.cpp_ty **
    (* TODO: add here sequential ownership of the lock, and maybe replace I by the lock invariant.
    Something like *)
    (* _mutex_field |-> mutex.R q ... ** *)
    pureR (cinv_own γ.(inv_gname) q).
  #[only(cfracsplittable)] derive R.
  #[global] Instance R_type_ptr `{Σ : cpp_logic, σ : genv, !lockedG Σ} γ q :
    Observe (type_ptrR T.cpp_ty) (R γ q).
  Proof. rewrite R.unlock. apply _. Qed.


  Section base_construction.
    Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
    Context {HAS_THREADS : HasStdThreads Σ}.
    Context `{!lockedG Σ}.

    #[global] Instance I_learn : Cbn (Learn (learn_eq ==> learn_hints.fin) I).
    Proof. solve_learnable. Qed.
    #[global] Instance R_learn : Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    Definition ctor_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
      \post Exists g, this |-> R g 1$m ** used_threads g empty).

    Definition dtor_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
      \pre{g} this |-> R g 1$m
      \pre used_threads g empty
      \post emp).

    Definition lock_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
        \prepost{q g} this |-> R g q (* part of both pre and post *)
        \persist{th} current_thread th
        \pre{Q} AC << ∀ n , locked g th n >> @ top \ ↑ mask , empty
                    << locked g th (S n) , COMM Q >>
        \post Q).

    Definition unlock_spec_body : ptr -> WpSpec mpred val val :=
      (\this this
        \prepost{q g} this |-> R g q (* part of both pre and post *)
        \persist{th} current_thread th
        \pre{Q} AC << ∀ n , locked g th (S n) >> @ top \ ↑ mask , empty
                    << locked g th n , COMM Q >>
        \post Q).

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

  Canonical Structure cmraR := excl_authR (prodO natO thread_idTO).

  Class recursive_mutexG `{Σ : cpp_logic} := {
    #[global] locked_G :: at_specs.lockedG Σ;
    #[global] level_own :: HasOwn (iPropI _Σ) cmraR;
  }.
  Definition G := @recursive_mutexG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance recursive_mutex_G `{Σ : cpp_logic} (H : G Σ) :
    @recursive_mutexG _ _ Σ := H.

  Definition rmutex_namespace :=
    nroot .@@ "std" .@@ "recursive_mutex" .@@ "derived".

  sl.lock
  Definition inv_rmutex `{Σ : cpp_logic, !G Σ}
      (g : gname) (P : mpred) : mpred :=
    cinv rmutex_namespace g.(cinv_gname)
      (Exists n th, own g.(level_gname) (●E (n, th)) **
        match n with
        | 0 => P ** own g.(level_gname) (◯E (n, th))
        | S n => at_specs.locked g.(lock_gname) th (S n)
        end).
  #[only(knowledge)] derive inv_rmutex.

  (** Fractional ownership of the physical recursive mutex and of the
   cancellable invariant that protects the custom resource P.
   The two fractions do not have to be the same, we just choose to make them
   equal for convenience.
  *)
  sl.lock
  Definition derivedR `{Σ : cpp_logic, σ : genv, !G Σ}
      (g : gname) (q : cQp.t) : Rep :=
    at_specs.R g.(lock_gname) q **
    pureR (cinv_own g.(cinv_gname) q).
  #[only(cfracsplittable)] derive derivedR.
  #[global] Instance derivedR_type_ptr `{Σ : cpp_logic, σ : genv, !G Σ} g q :
    Observe (type_ptrR cpp_ty) (derivedR g q).
  Proof. rewrite derivedR.unlock /cpp_ty. apply _. Qed.

  (** Public ownership packages the physical handle with its resource protocol. *)
  Definition R `{Σ : cpp_logic, !G Σ} {HAS_THREADS : HasStdThreads Σ}
      {σ : genv} (g : gname) (q : cQp.t) (P : mpred) : Rep :=
    derivedR g q ** pureR (inv_rmutex g P).
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(cfractional,cfracvalid,ascfractional)] derive R.
  #[global] Instance R_type_ptr `{Σ : cpp_logic, !G Σ}
      {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P :
    Observe (type_ptrR cpp_ty) (R g q P).
  Proof. rewrite /R. apply _. Qed.

  Definition used_threads `{Σ : cpp_logic, !G Σ, !HasStdThreads Σ}
      (g : gname) (threads : gset thread_idT) : mpred :=
    at_specs.used_threads g.(lock_gname) threads.
  #[global] Hint Opaque used_threads : sl_opacity typeclass_instances.
  #[only(timeless)] derive used_threads.

  Definition held_token `{Σ : cpp_logic, !G Σ}
      (g : gname) (th : thread_idT) (n : nat) : mpred :=
    own g.(level_gname) (◯E (S n, th)).
  #[global] Hint Opaque held_token : sl_opacity typeclass_instances.
  #[only(timeless)] derive held_token.

  Definition acquireable `{Σ : cpp_logic, !G Σ, !HasStdThreads Σ}
      (g : gname) (th : thread_idT) {TT : tele} (t : acquire_state TT)
      (P : TT -t> mpred) : mpred :=
    current_thread th **
    match t with
    | NotHeld => at_specs.locked g.(lock_gname) th 0
    | Held n args => held_token g th n ** tele_app P args
    end.

  #[global] Hint Opaque acquireable : sl_opacity typeclass_instances.

  Section rules.
    Context `{Σ : cpp_logic, !G Σ, !HasStdThreads Σ}.

    Lemma acquireable_Held g th {TT : tele} n (args : TT) P :
      acquireable g th (Held n args) P ⊣⊢
        current_thread th ** held_token g th n ** tele_app P args.
    Proof. rewrite /acquireable /=. done. Qed.

    #[global] Instance acquireable_current_thread :
      `{Observe (current_thread th) (acquireable g th (TT := TT) t P)}.
    Proof. rewrite /acquireable; apply _. Qed.

    Lemma use_thread_acquirable {TT} th g m P :
      th ∉ m ->
      current_thread th ** used_threads g m |-- (|==>
        used_threads g (m ∪ {[th]}) ** acquireable (TT := TT) g th NotHeld P).
    Proof.
      rewrite /used_threads /acquireable /=.
      work. wapply at_specs.use_thread; first done.
      work with br_erefl. iModIntro; work.
    Qed.

    Lemma logout_acquirable {TT} th g m P :
      th ∉ m ->
      used_threads g (m ∪ {[th]}) ** acquireable (TT := TT) g th NotHeld P |--
        (|==> used_threads g m).
    Proof.
      rewrite /used_threads /acquireable /=.
      iIntros (Hnot) "[HU [_ HL]]".
      iMod (at_specs.logout th g.(lock_gname) m Hnot
        with "[$HU $HL]") as "(HU & Hunit)".
      iModIntro.
      iFrame "HU". iApply (affine with "Hunit"). apply mpred_BiAffine.
    Qed.
  End rules.
End RecursiveMutexPreds.

(** Atomic specs derive the non-atomic specs. *)
Module RecursiveMutexRefinement (T : MutexCPPName).
  Module Preds := RecursiveMutexPreds T.
  Module Spec := recursive_mutex_spec T Preds.
  Import Preds.

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
    rewrite /acquireable /=.
    iMod (own_alloc (●E (O, th) ⋅ ◯E (O, th))) as (g) "(? & ?)".
    { apply excl_auth_valid. }
    wname [Preds.at_specs.used_threads] "u".
    wname [_ |-> _ _ _] "a".
    iMod (cinv_alloc with "[-u a]") as (ginv) "(#Hinv & Hown)"; last first.
    - iExists {| lock_gname := t; level_gname := g; cinv_gname:= ginv |}.
      rewrite /R /used_threads _at_sep _at_pureR derivedR.unlock inv_rmutex.unlock /=.
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
    rewrite /R /used_threads _at_sep _at_pureR derivedR.unlock inv_rmutex.unlock.
    work.
    iMod (cinv_cancel with "[$] [$]") as (n th) "(>? & ?)"; [done..|].

    destruct n as [|n'] eqn:?; work; first last.
    {
      rewrite Preds.at_specs.locked.unlock /used_threads Preds.at_specs.used_threads.unlock.
      wapply lock_ghost.used_threads_empty_no_not_locked; work with br_erefl.
    }
    iModIntro. work. iModIntro. ego with br_erefl.
    (* _now_ we just need to leak ghost state and that's okay *)
    wname [own] "L1"; wname [own] "L2"; iCombine "L1 L2" as "L".
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
    rewrite /R _at_sep _at_pureR derivedR.unlock; work.
    iExists q, (cinv_own g.(cinv_gname) q **
      (∃ t, [| acquire n t |] ∗ ▷ acquireable g th t P))%I.
    wname [bi_wand] "W"; wfocus (bi_wand _ _) "W". { work $usenamed=true. }
    rewrite inv_rmutex.unlock /acquireable /held_token.
    work; iAcIntro; rewrite /commit_acc/=; work.
    iInv rmutex_namespace as "[(%n' & %th' & >Hn & Hcases) ?]" "Hclose".
    destruct n as [|n args]; simpl; [iExists 0 | iExists (S n)]; work.
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
        first apply (excl_auth_update _ _ (1, th)).
      wname [Preds.at_specs.locked _ th _] "Hlocked";
        iMod ("Hclose" with "[$Hg $Hlocked //]") as "_"; iModIntro.
      iExists (Held 0 args). work.
    - iMod (own_update_2 with "Hn [$]") as "(Hg & ?)";
        first apply (excl_auth_update _ _ (S (S n), th)).
      wname [Preds.at_specs.locked _ th _] "Hlocked";
        iMod ("Hclose" with "[$Hg $Hlocked //]") as "_"; iModIntro.
      iExists (Held (S n) args). work.
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
    rewrite /R _at_sep _at_pureR derivedR.unlock; work.
    iExists q, (cinv_own g.(cinv_gname) q **
      acquireable g th (release $ Held n args) P)%I.
    wname [bi_wand] "W"; wfocus (bi_wand _ _) "W". { work $usenamed=true. }
    rewrite inv_rmutex.unlock /acquireable /held_token.
    work; iAcIntro; rewrite /commit_acc/=; work.
    iInv rmutex_namespace as "[(%n' & %th' & >Hn & Hcases) ?]" "Hclose".
    iDestruct (own_valid_2 with "Hn [$]") as %[=]%excl_auth_agree_L; subst.
    iMod "Hcases".
    iApply fupd_mask_intro; first set_solver; iIntros "Hclose'".
    iExists n; work $usenamed=true.
    iMod "Hclose'" as "_".
    iMod (own_update_2 with "Hn [$]") as "(Hg & Hcase)";
      first apply (excl_auth_update _ _ (n, th)).
    rewrite release.unlock; destruct n; iFrame "#∗".
    all: iMod ("Hclose" with "[-]") as "_";
      ework $usenamed=true with br_erefl; done.
  Qed.

End with_cpp.
End RecursiveMutexRefinement.
