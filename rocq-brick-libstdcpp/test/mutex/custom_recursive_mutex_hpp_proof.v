(** Verification of the recursive wrapper around std::mutex.

    The implementation clears the atomic owner before releasing the inner
    mutex. The contracts are partial-correctness contracts: at the largest
    counter value, lock does not return. Hash uniqueness is assumed by
    [thread.spec] in the shared thread specifications. The lock/unlock
    contracts instantiate [recursive_mutex_spec], including its
    [BasicLockable] presentation and construction contracts. *)
Require Import iris.algebra.coPset.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.atomic.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.
Require Import skylabs.brick.libstdcpp.thread.spec.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.test.mutex.custom_recursive_mutex_hpp.

Import linearity.

Module CustomRecursiveMutexName <: MutexCPPName.
  Definition cpp_ty : type := "MyRecursiveMutex"%cpp_type.
End CustomRecursiveMutexName.

(* A custom recursive mutex implementation built on top of a mutex.
   The definition for [token] and [not_locked] coincide with the ones in the 
   MutexPreds module. *)
Module CustomRecursiveMutexPreds
    <: RECURSIVE_MUTEX_PREDS CustomRecursiveMutexName.
  Include RecursiveMutexState.

  Definition class_name : name := "MyRecursiveMutex"%cpp_name.
  Definition cpp_ty : type := CustomRecursiveMutexName.cpp_ty.

  Record mutex_gname : Set := MkGname {
    inner_gname : mutex.gname;
    owner_gname : iprop.gname;
    cinv_gname : iprop.gname;
  }.
  Definition gname : Set := mutex_gname.
  Definition pool_name (g : gname) : iprop.gname :=
    mutex.pool_name g.(inner_gname).
  Definition rmutex_inv_namespace (g : gname) : namespace :=
    mutex.mutex_inv_namespace g.(inner_gname).

  (** If there is [Some] owner, it records the thread ID [th] and the fraction
     in the lock handle [acquireable] for thread [th]. *)
  Canonical Structure owner_cmraR : cmra :=
    excl_authR (optionO (prodO thread_idTO (leibnizO cQp.t))).

  Class stateG `{Σ : cpp_logic} := {
    #[global] mutex_G :: mutex.G Σ;
    #[local] has_owner_own :: HasOwn (iPropI _Σ) owner_cmraR;
    #[local] has_owner_upd :: HasOwnUpd (iPropI _Σ) owner_cmraR;
    #[local] has_owner_valid :: HasOwnValid (iPropI _Σ) owner_cmraR;
  }.
  Definition G := @stateG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance state_G `{Σ : cpp_logic} (H : G Σ) : @stateG _ _ Σ := H.

  #[global] Instance sets_G `{Σ : cpp_logic, !G Σ} : MutexSets.G Σ := _.

  Definition owner_tid_auth `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (o : option (thread_idT * cQp.t)) : mpred :=
    own γ ((●E o) : owner_cmraR).
  Definition owner_tid_frag `{Σ : cpp_logic, !G Σ}
      (γ : iprop.gname) (o : option (thread_idT * cQp.t)) : mpred :=
    own γ ((◯E o) : owner_cmraR).

  #[global] Instance owner_tid_auth_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_auth γ o).
  Proof. rewrite /owner_tid_auth. apply _. Qed.
  #[global] Instance owner_tid_frag_timeless
      `{Σ : cpp_logic, !G Σ} γ o : Timeless (owner_tid_frag γ o).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_tid_frag_exclusive
      `{Σ : cpp_logic, !G Σ} γ : Exclusive1 (owner_tid_frag γ).
  Proof.
    intros o1 o2. rewrite /owner_tid_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid. rewrite excl_auth_frag_op_valid. done.
  Qed.

  #[global] Instance owner_tid_auth_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_auth γ o).
  Proof. rewrite /owner_tid_auth. apply _. Qed.
  #[global] Instance owner_tid_frag_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} γ o : WeaklyObjective (owner_tid_frag γ o).
  Proof. rewrite /owner_tid_frag. apply _. Qed.

  #[global] Instance owner_agree `{Σ : cpp_logic, !G Σ} γ o1 o2 :
    Observe2 [| o1 = o2 |] (owner_tid_auth γ o1) (owner_tid_frag γ o2).
  Proof.
    apply observe_2_intro_only_provable.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "A F".
    iDestruct (own_valid_2 with "A F") as %HV.
    iPureIntro. apply leibniz_equiv, excl_auth_agree, HV.
  Qed.

  Lemma owner_alloc `{Σ : cpp_logic, !G Σ} o :
    ⊢ |==> ∃ γ, owner_tid_auth γ o ** owner_tid_frag γ o.
  Proof.
    iMod (own_alloc ((●E o ⋅ ◯E o) : owner_cmraR)) as (γ) "H".
    { apply excl_auth_valid. }
    iModIntro. iExists γ.
    rewrite /owner_tid_auth /owner_tid_frag -own_op. iExact "H".
  Qed.

  Lemma owner_update `{Σ : cpp_logic, !G Σ} γ oa ofrag o' :
    owner_tid_auth γ oa ** owner_tid_frag γ ofrag |--
      (|==> owner_tid_auth γ o' ** owner_tid_frag γ o').
  Proof.
    rewrite /owner_tid_auth /owner_tid_frag. iIntros "[A F]".
    iMod (own_update_2 with "A F") as "[$ $]";
      first apply (excl_auth_update _ _ o').
    done.
  Qed.

  #[global] Hint Opaque owner_tid_auth owner_tid_frag : sl_opacity typeclass_instances.

  Definition token `{Σ : cpp_logic, !G Σ} (g : gname) (q : cQp.t) : mpred :=
    mutex.token g.(inner_gname) q.
  #[global] Hint Opaque token : sl_opacity typeclass_instances.

  #[global] Instance token_fractional `{Σ : cpp_logic, !G Σ} g :
    CFractional (token g).
  Proof. intros q1 q2. rewrite /token. apply mutex.token_fractional. Qed.
  #[global] Instance token_timeless `{Σ : cpp_logic, !G Σ} g qt :
    Timeless (token g qt).
  Proof. rewrite /token. apply _. Qed.

  Definition owner_frag `{Σ : cpp_logic, !G Σ}
      (g : gname) (owner : option (thread_idT * cQp.t)) : mpred :=
    owner_tid_frag g.(owner_gname) owner.

  Definition countR `{Σ : cpp_logic, σ : genv}
      (this : ptr) (n : Z) : mpred :=
    this ,, _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m n.

  Definition protected `{Σ : cpp_logic, !G Σ, σ : genv}
      (this : ptr) (go : iprop.gname) (P : mpred) : mpred :=
    countR this 0 ** owner_tid_frag go None ** P.

  Definition globals `{Σ : cpp_logic, σ : genv} (q : cQp.t) : mpred :=
    _global "id_hash" |-> ulongR q (thread_id_specs.thread_id_hash thread_id_specs.default_thread_id).
  #[global] Arguments globals /.

  (** Absence of a ghost owner is encoded by the default C++ thread ID. *)
  Definition owner_id (owner : option (thread_idT * cQp.t)) : thread_idT :=
    match owner with
    | None => thread_id_specs.default_thread_id
    | Some (th, _) => th
    end.

  Definition I `{Σ : cpp_logic, !G Σ, σ : genv}
      (this : ptr) (g : gname) : mpred :=
    ∃ owner,
      this ,, _field "MyRecursiveMutex::m_owner" |->
        atomic.R Tulong 1$m (thread_id_specs.thread_id_hash (owner_id owner)) **
      owner_tid_auth g.(owner_gname) owner **
      match owner with
      | Some (th, qt) =>
        (** Note that this [mutex.locked] is NOT the [locked] precidate that we
        instantiate later for the CustomRecursiveMutexPreds.

        Putting [mutex.locked] here is useful when a thread [th] acquires the
        lock for the first time to show that [owner ≠ th]:  when [th] opens
        the invariant, [th] has [CustomRecursiveMutexPreds.not_locked th]
        (which coincide with [mutex.not_locked th]), contradicting
        [mutex.locked _ _ th _]. *)
         mutex.locked
          (this ,, _field "MyRecursiveMutex::m_lock") g.(inner_gname) th qt
      | None => emp
      end.

  Definition R `{Σ : cpp_logic, !G Σ}
      {HAS_THREADS : HasStdThreads Σ} {σ : genv}
      (g : gname) (q : cQp.t) (P : mpred) : Rep :=
    structR class_name q$m **
    as_Rep (fun this =>
      this ,, _field "MyRecursiveMutex::m_lock" |->
        mutex.R g.(inner_gname) q (protected this g.(owner_gname) P) **
      cinv (rmutex_inv_namespace g) g.(cinv_gname) (I this g) **
      cinv_own g.(cinv_gname) q).
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(type_ptr,cfractional,ascfractional,cfracvalid)] derive R.

  #[global] Instance R_learnable
      `{Σ : cpp_logic, !G Σ, σ : genv, !HasStdThreads Σ} :
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
  Proof. solve_learnable. Qed.

  Definition not_locked `{Σ : cpp_logic, !G Σ, σ : genv}
      (this : ptr) (g : gname) (qt : cQp.t) (th : thread_idT) : mpred :=
    mutex.not_locked (this ,, _field "MyRecursiveMutex::m_lock") g.(inner_gname) th qt.

  Definition locked `{Σ : cpp_logic, !G Σ, σ : genv}
      (this : ptr) (g : gname) (qt : cQp.t) (th : thread_idT)
      (n : nat) : mpred :=
    countR this (Z.of_nat (S n)) ** owner_frag g (Some (th, qt)).

  #[global] Hint Opaque not_locked locked : sl_opacity typeclass_instances.

  #[global] Instance I_timeless
      `{Σ : cpp_logic, !G Σ, σ : genv} this g : Timeless (I this g).
  Proof.
    rewrite /I. apply bi.exist_timeless.
    intros [[th qt]|]; apply _.
  Qed.

  #[global] Instance owner_frag_timeless
      `{Σ : cpp_logic, !G Σ} g owner : Timeless (owner_frag g owner).
  Proof. rewrite /owner_frag. apply _. Qed.
  #[global] Instance locked_timeless
      `{Σ : cpp_logic, !G Σ, σ : genv} this g qt th n :
      Timeless (locked this g qt th n).
  Proof. rewrite /locked /countR. apply _. Qed.
  #[global] Instance not_locked_timeless
      `{Σ : cpp_logic, !G Σ, σ : genv} this g qt th :
      Timeless (not_locked this g qt th).
  Proof. rewrite /not_locked. apply _. Qed.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
      WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.

  #[global] Instance owner_frag_WeaklyObjective
      `{Σ : cpp_logic, !G Σ} g owner : WeaklyObjective (owner_frag g owner).
  Proof. rewrite /owner_frag. apply _. Qed.
  #[global] Instance I_WeaklyObjective
      `{Σ : cpp_logic, !G Σ, σ : genv} this g :
      WeaklyObjective (I this g).
  Proof.
    rewrite /I. apply exists_weakly_objective.
    intros [[th qt]|]; apply _.
  Qed.
  #[global] Instance protected_WeaklyObjective
      `{Σ : cpp_logic, !G Σ, σ : genv} this go P
      `{!WeaklyObjective (countR this 0), !WeaklyObjective P} :
      WeaklyObjective (protected this go P).
  Proof. rewrite /protected. apply _. Qed.

  Lemma register_thread `{Σ : cpp_logic, !G Σ, σ : genv}
      (this : ptr) g th qt :
    token g qt **
    MutexSets.my_mutexes (pool_name g) th (CoPset $ ↑rmutex_inv_namespace g) ⊣⊢
    not_locked this g qt th.
  Proof.
    rewrite /token /not_locked /pool_name /rmutex_inv_namespace.
    apply mutex.register_thread.
  Qed.

End CustomRecursiveMutexPreds.

Module custom_recursive_mutex.
  Import CustomRecursiveMutexPreds.
  Module Spec := recursive_mutex_spec
    CustomRecursiveMutexName CustomRecursiveMutexPreds.
  Import Spec (acquireable).
  #[local] Hint Opaque acquireable I protected countR : sl_opacity typeclass_instances.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !G Σ}.
    Context `{MOD : source ⊧ σ}.

    (** The wrapper adds its global sentinel and the count's objectivity
        requirement to the shared recursive-mutex construction contract. *)
    cpp.spec "MyRecursiveMutex::MyRecursiveMutex()" as ctor_spec with (
      \this this
      \prepost{qg} globals qg
      \require WeaklyObjective (countR this 0)
      \exact Reduce (Spec.ctor_spec this)).

    cpp.spec "MyRecursiveMutex::~MyRecursiveMutex()" as dtor_spec with
      (\exact Reduce Spec.dtor_spec).

    cpp.spec "MyRecursiveMutex::lock()" as lock_spec from source with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.lock_spec this)).

    cpp.spec "MyRecursiveMutex::unlock()" as unlock_spec from source with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.unlock_spec this)).

    cpp.spec "MyRecursiveMutex::lock()" as lock_spec_alt from source with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.lock_spec_alt this)).

    cpp.spec "MyRecursiveMutex::unlock()" as unlock_spec_alt from source with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.unlock_spec_alt this)).

    (* Helper specs, proved later. *)
    cpp.spec "std::mutex::lock()" as inner_lock_spec with (
      \this inner
      \prepost{(container : ptr) g q P} container |-> R g q P
      \require inner = container ,, _field "MyRecursiveMutex::m_lock"
      \persist{th} current_thread th
      \pre{qt} not_locked container g qt th
      \post protected container g.(owner_gname) P ** mutex.locked inner g.(inner_gname) th qt).

    cpp.spec "std::mutex::unlock()" as inner_unlock_spec with (
      \this inner
      \prepost{(container : ptr) g q P} container |-> R g q P
      \require inner = container ,, _field "MyRecursiveMutex::m_lock"
      \persist{th} current_thread th
      \pre{qt} mutex.locked inner g.(inner_gname) th qt
      \pre ▷ protected container g.(owner_gname) P
      \post not_locked container g qt th).

    (* The proof bodies in the rest of the section are generated by LLM. *)
    Lemma ctor_proof : verify[source] ctor_spec.
    Proof using MOD.
      (* Initialize the physical members first, with an empty inner invariant. *)
      verify_spec.
      (* Retain the final statement so its update modality can install the
         ghost state after the member constructors return. *)
      match goal with |- context[wp ?tu ?rho ?s ?K] =>
        rewrite (lock (wp tu rho s K)) end.
      go. iExists emp. go.
      rewrite -lock.
      iApply fupd_wp.
      iDestruct select (|={⊤}=> _)%I as "Init".
      iMod "Init" as (g) "[Inner Token]".
      (* Install the zero count, empty owner fragment, and client resource in
         the inner mutex; keep the matching authority with the atomic owner. *)
      iMod (owner_alloc None) as (go) "[Auth Frag]".
      wname [_ |-> ulonglongR _ _] "Count".
      iDestruct select (tele_app P xs) as "P".
      iMod (mutex.init_R (this ,, _field "MyRecursiveMutex::m_lock")
        g pool N (protected this go (∃ xs, tele_app P xs))
        with "[Inner Token Count Frag P]") as (inner) "(%Hnames & Inner & Token)".
      { iFrame "Inner Token". iNext. rewrite /protected /countR. iFrame. }
      wname [_ |-> atomic.R _ _ _] "Owner".
      iMod (cinv_alloc ⊤ (mutex.mutex_inv_namespace inner) with "[Owner Auth]") as (gi) "[#CI CO]"; last first.
      - iModIntro. go. iExists (MkGname inner go gi).
        iSplit; first (iPureIntro; split; reflexivity).
        rewrite /token /R _at_sep _at_as_Rep
          /I /pool_name /=.
        iFrame "CI". iFrame.
      - iNext. rewrite /I /=. iExists None. iFrame.
      - change (WeaklyObjective (I this (MkGname inner go 1%positive))).
        apply _.
    Qed.

    Lemma dtor_proof :
      mutex.dtor_spec ** std.atomic.dtor Tulong |-- verify[source] dtor_spec.
    Proof using MOD.
      verify_shift.
      rewrite /token /R _at_sep _at_as_Rep.
      work.
      wname [cinv] "#CI".
      wname [cinv_own] "CO".
      (* Cancel the owner invariant before destroying the physical members. *)
      iMod (cinv_cancel with "CI CO") as "Inv"; [done..|].
      iEval (rewrite /I) in "Inv".
      iMod "Inv" as (owner) "[Owner State]".
      iModIntro. go.
      iAssert emp with "[State]" as "_".
      { iApply (affine with "[State]"); last iAccu. apply mpred_BiAffine. }
      (* The inner mutex destructor returns the protected count and resource. *)
      wname [protected] "Guard".
      iEval (rewrite /protected /countR) in "Guard".
      iDestruct "Guard" as "(Count & Frag & P)".
      iAssert emp with "[Frag]" as "_".
      { iApply (affine with "[Frag]"); last iAccu. apply mpred_BiAffine. }
      ego $usenamed=true with br_erefl.
    Qed.

    #[local] Existing Instance mpred_BiAffine.
    #[local] Hint Opaque owner_frag locked not_locked
      : sl_opacity typeclass_instances.
    #[local] Instance owner_frag_learn : LearnEq2 owner_frag.
    Proof. solve_learnable. Qed.

    Abbreviation BASE p :=
      (p ,, _base "std::atomic<unsigned long>" "std::__atomic_base<unsigned long>").

    Lemma inner_lock_spec_ok : mutex.lock_spec_alt |-- inner_lock_spec.
    Proof.
      apply specify_mono. rewrite /R /not_locked. work with br_erefl.
      iExists qt. work with br_erefl.
    Qed.

    Lemma inner_unlock_spec_ok : mutex.unlock_spec_alt |-- inner_unlock_spec.
    Proof.
      apply specify_mono. rewrite /R /not_locked. work with br_erefl.
      iExists qt. work with br_erefl.
    Qed.

    #[program]
    Definition load_not_held_C (this : ptr) :=
      \cancelx
      \consuming{g q P} this |-> R g q P
      \consuming{th qt} not_locked this g qt th
      \guard (th <> thread_id_specs.default_thread_id)
      \proving{K (_ : IsExistential K)}
        std.atomic.do_load Tulong (BASE (this ,, _field "MyRecursiveMutex::m_owner")) K
      \instantiate K := (fun owner => this |-> R g q P **
        not_locked this g qt th ** [| owner <> thread_id_specs.thread_id_hash th |])
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[HR Hhandle]" (?? ->).
      iEval (rewrite /R _at_sep _at_as_Rep) in "HR".
      iDestruct "HR" as "(S & Base & #CI & CO)".
      rewrite /std.atomic.do_load.
      iAcIntro. rewrite /commit_acc.
      iInv (rmutex_inv_namespace g) as "[>Inv CO]" "Hclose".
      iEval (rewrite /I) in "Inv".
      iDestruct "Inv" as (owner) "(Owner & Auth & Handle)".
      iAssert [| option_map fst owner <> Some th |] as %Hne.
      { destruct owner as [[owner owner_qt]|]; last (iPureIntro; simpl; congruence).
        destruct (decide (owner = th)) as [->|Hne]; last (iPureIntro; simpl; congruence).
        iEval (rewrite /not_locked) in "Hhandle".
        iDestruct (mutex.Spec.locked_not_locked_exclusive with "[$Handle $Hhandle]") as %[]. }
      iDestruct (fupd_mask_subseteq) as ">Y"; [| iModIntro]; first set_solver.
      iExists (thread_id_specs.thread_id_hash (owner_id owner)), (1$m)%cQp.
      iSplitL "Owner"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "Owner". iMod "Y" as "_".
      iMod ("Hclose" with "[Owner Auth Handle]") as "_".
      { iNext. rewrite /I. iExists owner.
        iSplitL "Owner"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /R /owner_frag _at_sep _at_as_Rep. iFrame "#∗".
      iPureIntro. intros Heq.
      apply thread_id_specs.thread_id_hash_injective in Heq.
      destruct owner as [[owner owner_qt]|]; simpl in Heq, Hne; naive_solver.
    Qed.
    #[local] Hint Resolve load_not_held_C : sl_opacity.

    #[program]
    Definition load_held_C (this : ptr) :=
      \cancelx
      \consuming{g q P} this |-> R g q P
      \consuming{th qt} owner_frag g (Some (th, qt))
      \proving{K (_ : IsExistential K)}
        std.atomic.do_load Tulong (BASE (this ,, _field "MyRecursiveMutex::m_owner")) K
      \instantiate K := (fun owner => this |-> R g q P **
        owner_frag g (Some (th, qt)) ** [| owner = thread_id_specs.thread_id_hash th |])
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[HR Hfrag]" (?? ->).
      iEval (rewrite /R _at_sep _at_as_Rep) in "HR".
      iDestruct "HR" as "(S & Base & #CI & CO)".
      rewrite /std.atomic.do_load.
      iAcIntro. rewrite /commit_acc.
      iInv (rmutex_inv_namespace g) as "[>Inv CO]" "Hclose".
      iEval (rewrite /I) in "Inv".
      iDestruct "Inv" as (owner) "(Owner & Auth & Handle)".
      iEval (rewrite /owner_frag) in "Hfrag".
      iDestruct (observe_2 [| owner = Some (th, qt) |] with "Auth Hfrag") as %->.
      iDestruct (fupd_mask_subseteq) as ">Y"; [| iModIntro]; first set_solver.
      iExists (thread_id_specs.thread_id_hash th), (1$m)%cQp.
      iSplitL "Owner"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "Owner". iMod "Y" as "_".
      iMod ("Hclose" with "[Owner Auth Handle]") as "_".
      { iNext. rewrite /I. iExists (Some (th, qt)).
        iSplitL "Owner"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /R /owner_frag _at_sep _at_as_Rep. iFrame "#∗". done.
    Qed.
    #[local] Hint Resolve load_held_C : sl_opacity.

    Lemma store_owner_action (this : ptr) g q P th qt :
      this |-> R g q P ** owner_tid_frag g.(owner_gname) None **
        mutex.locked (this ,, _field "MyRecursiveMutex::m_lock") g.(inner_gname) th qt |--
      std.atomic.do_store Tulong (BASE (this ,, _field "MyRecursiveMutex::m_owner"))
        (thread_id_specs.thread_id_hash th) (this |-> R g q P ** owner_frag g (Some (th, qt))).
    Proof using Type MOD.
      iIntros "(HR & Hfrag & Hhandle)".
      iEval (rewrite /R _at_sep _at_as_Rep) in "HR".
      iDestruct "HR" as "(S & Base & #CI & CO)".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc.
      iInv (rmutex_inv_namespace g) as "[>Inv CO]" "Hclose".
      iEval (rewrite /I) in "Inv".
      iDestruct "Inv" as (owner) "(Owner & Auth & Handle)".
      iEval (rewrite /owner_frag) in "Hfrag".
      iDestruct (observe_2 [| owner = None |] with "Auth Hfrag") as %->.
      iDestruct (fupd_mask_subseteq) as ">Y"; [| iModIntro]; first set_solver.
      iExists (thread_id_specs.thread_id_hash thread_id_specs.default_thread_id).
      iSplitL "Owner"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "Owner". iMod "Y" as "_".
      iMod (owner_update (owner_gname g) None None (Some (th, qt))
        with "[$Auth $Hfrag]") as "[Auth Hfrag]".
      iMod ("Hclose" with "[Owner Auth Hhandle]") as "_".
      { iNext. rewrite /I. iExists (Some (th, qt)).
        iSplitL "Owner"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /R /owner_frag _at_sep _at_as_Rep. iFrame "#∗".
    Qed.

    #[program]
    Definition store_owner_C (this : ptr) :=
      \cancelx
      \consuming{g q P} this |-> R g q P
      \consuming owner_tid_frag g.(owner_gname) None
      \consuming{th qt} mutex.locked
        (this ,, _field "MyRecursiveMutex::m_lock") g.(inner_gname) th qt
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store Tulong (BASE (this ,, _field "MyRecursiveMutex::m_owner")) (thread_id_specs.thread_id_hash th) K
      \instantiate K := (this |-> R g q P ** owner_frag g (Some (th, qt)))
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "Hpre" (?? ->). iApply (store_owner_action with "Hpre").
    Qed.
    #[local] Hint Resolve store_owner_C : sl_opacity.

    Lemma clear_owner_action (this : ptr) g q P th qt :
      this |-> R g q P ** owner_frag g (Some (th, qt)) |--
      std.atomic.do_store Tulong (BASE (this ,, _field "MyRecursiveMutex::m_owner"))
        (thread_id_specs.thread_id_hash thread_id_specs.default_thread_id) (this |-> R g q P ** owner_frag g None **
          mutex.locked (this ,, _field "MyRecursiveMutex::m_lock") g.(inner_gname) th qt).
    Proof using Type MOD.
      iIntros "[HR Hfrag]".
      iEval (rewrite /R _at_sep _at_as_Rep) in "HR".
      iDestruct "HR" as "(S & Base & #CI & CO)".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc.
      iInv (rmutex_inv_namespace g) as "[>Inv CO]" "Hclose".
      iEval (rewrite /I) in "Inv".
      iDestruct "Inv" as (owner) "(Owner & Auth & Handle)".
      iEval (rewrite /owner_frag) in "Hfrag".
      iDestruct (observe_2 [| owner = Some (th, qt) |] with "Auth Hfrag") as %->.
      iDestruct (fupd_mask_subseteq) as ">Y"; [| iModIntro]; first set_solver.
      iExists (thread_id_specs.thread_id_hash th).
      iSplitL "Owner"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "Owner". iMod "Y" as "_".
      iMod (owner_update (owner_gname g) (Some (th, qt)) (Some (th, qt)) None
        with "[$Auth $Hfrag]") as "[Auth Hfrag]".
      iMod ("Hclose" with "[Owner Auth]") as "_".
      { iNext. rewrite /I. iExists None.
        iSplitL "Owner"; first by ework $usenamed=true with br_erefl. iFrame. }
      iModIntro. rewrite /R /owner_frag _at_sep _at_as_Rep. iFrame "#∗".
    Qed.

    #[program]
    Definition clear_owner_C (this : ptr) :=
      \cancelx
      \consuming{g q P} this |-> R g q P
      \consuming{th qt} owner_frag g (Some (th, qt))
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store Tulong (BASE (this ,, _field "MyRecursiveMutex::m_owner")) (thread_id_specs.thread_id_hash thread_id_specs.default_thread_id) K
      \instantiate K := (this |-> R g q P ** owner_frag g None **
          mutex.locked (this ,, _field "MyRecursiveMutex::m_lock") g.(inner_gname) th qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "Hpre" (?? ->). iApply (clear_owner_action with "Hpre").
    Qed.
    #[local] Hint Resolve clear_owner_C : sl_opacity.

    Lemma lock_spec_equiv_lock_spec_alt : lock_spec ⊣⊢ lock_spec_alt.
    Proof.
      rewrite /lock_spec /lock_spec_alt /specify.
      do 2 f_equiv. intros this xs K.
      rewrite !add_with_equiv. f_equiv=> qg.
      by rewrite !add_prepost_equiv Spec.lock_spec_equiv_lock_spec_alt.
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt : unlock_spec ⊣⊢ unlock_spec_alt.
    Proof.
      rewrite /unlock_spec /unlock_spec_alt /specify.
      do 2 f_equiv. intros this xs K.
      rewrite !add_with_equiv. f_equiv=> qg.
      by rewrite !add_prepost_equiv Spec.unlock_spec_equiv_unlock_spec_alt.
    Qed.

    Lemma lock_proof : verify[source] lock_spec.
    Proof using MOD.
      verify_spec.
      rewrite /acquireable. destruct n as [|n xs].
      (* First acquisition: exclude our own ID, then acquire the inner mutex. *)
      - ego.
        (* Publishing ownership transfers the inner held capability into the
           owner invariant; its fragment remembers the registration share. *)
        rewrite /protected. ego.
        iDestruct select (this |-> R _ _ _) as "HR".
        iDestruct select (owner_tid_frag _ None) as "Hfrag".
        iDestruct select (mutex.locked _ _ _ _) as "Hinner".
        iDestruct (store_owner_action with "[$HR $Hfrag $Hinner]") as "Hstore".
        iSplitL "Hstore"; first iExact "Hstore". ego.
        rewrite /countR. ego.
        rewrite /acquireable /locked /countR. ego.
        wname [P] "HP". iExact "HP".
      (* Recursive acquisition: the owner fragment identifies this thread. *)
      - rewrite /locked /countR. ego.
        destruct (decide (Z.of_nat (S n) = 18446744073709551615)%Z) as [Hmax|Hmax]; go.
        (* At the counter limit, the loop has no returning execution. *)
        + rewrite Hmax. go. wp_for (fun _ => emp); go.
        + ego. rewrite /acquireable /locked /countR.
          have Hcount : (Z.of_nat (S n) + 1)%Z = Z.of_nat (S (S n)) by lia.
          rewrite Hcount. iFrame "#∗".
    Qed.

    Lemma unlock_proof : verify[source] unlock_spec.
    Proof using MOD.
      verify_spec.
      rewrite /acquireable /locked /countR.
      go.
      destruct n as [|n].
      (* Final release: clear the owner to recover the inner held capability;
         the inner unlock then returns the acquisition handle. *)
      - ego.
        (* Return the zero count and client resource to the inner mutex. *)
        wname [mutex.locked] "Locked". iFrame "Locked".
        wname [P] "P".
        wname [_ |-> ulonglongR _ _] "Count".
        wname [owner_frag] "OF".
        iSplitL "P Count OF".
        { iNext. rewrite /protected /countR /owner_frag.
          iFrame "Count OF". iExists args. iExact "P". }
        ego. rewrite /acquireable release.unlock. iFrame "#∗".
      (* Nested release: decrement the count and keep the resource. *)
      - ego. rewrite /acquireable release.unlock /locked /countR.
        have Hcount : (Z.of_nat (S (S n)) - 1)%Z = Z.of_nat (S n) by lia.
        rewrite Hcount. iFrame "#∗".
    Qed.

    Lemma lock_alt_proof : verify[source] lock_spec_alt.
    Proof using MOD.
      rewrite -lock_spec_equiv_lock_spec_alt. exact lock_proof.
    Qed.

    Lemma unlock_alt_proof : verify[source] unlock_spec_alt.
    Proof using MOD.
      rewrite -unlock_spec_equiv_unlock_spec_alt. exact unlock_proof.
    Qed.

    Local Lemma id_dtor_ok : verify[source] thread_id_specs.thread_id_dtor_spec.
    Proof using MOD. verify_spec. rewrite thread_id_specs.thread_idR.unlock. go. Qed.

    (** Only the out-of-line hash primitive and native-ID call remain library
        premises for thread IDs. The hash wrappers and destructors are proved
        in [thread.spec]. *)
    Definition standard_library_specs : mpred :=
      denoteModule thread_hpp.source **
      mutex.ctor_spec ** mutex.dtor_spec **
      mutex.lock_spec_alt ** mutex.unlock_spec_alt **
      std.atomic.ctor Tulong ** std.atomic.dtor Tulong **
      std.atomic.cast Tulong ** std.atomic.assign Tulong **
      thread_id_specs.get_id_spec **
      thread_id_specs.hash_bytes_spec **
      std.cassert.assert_fail_spec.

    Lemma link :
      denoteModule source ** standard_library_specs |--
      ctor_spec ** dtor_spec ** lock_spec ** unlock_spec.
    Proof using MOD.
      rewrite /standard_library_specs.
      iIntros "[Hsource [#Hthread Hspecs]]".
      iDestruct (observe [| thread_hpp.source ⊧ σ |] with "Hthread") as "%THREADMOD".
      iCombine "Hsource Hthread Hspecs" as "Hpre". iRevert "Hpre".
      work.
      wapply ctor_proof.
      wapply dtor_proof.
      wapply lock_proof.
      wapply unlock_proof.
      wapply inner_lock_spec_ok.
      wapply inner_unlock_spec_ok.
      wapply id_dtor_ok.
      wapply (thread_id_specs.hash_link (MOD := THREADMOD)).
      work.
    Qed.

  End with_cpp.

End custom_recursive_mutex.
