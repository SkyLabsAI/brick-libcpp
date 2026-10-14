(** Provisional *)

Require Import iris.algebra.coPset.
Require Import iris.algebra.frac.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.base_derived.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.atomic.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.thread.spec.
NES.Open std.atomic.

Import linearity.
Import OwnerTid.
Require Import skylabs.brick.libstdcpp.test.mutex.custom_mutex_hpp.

(** The concrete mutex supplies both the ghost state and the physical
    predicates used by [mutex_spec]. The mutex-set pool is shared, and the
    memory-order global remains a separate precondition of the C++ methods. *)
Module CustomMutexPreds <: MUTEX_PREDS.
  Import MutexSets.

  Record state_gname : Set := MkStateGname {
    token_gname : iprop.gname;
    owner_gname : iprop.gname;
    state_namespace : namespace;
    state_namespace_not_root : state_namespace <> nroot;
  }.

  Definition class_name : name := "MyMutex"%cpp_name.
  Definition cpp_ty : type := Tnamed class_name.
  Record mutex_gname : Set := MkGname {
    lock_state_gname :> state_gname;
    cinv_gname : iprop.gname;
  }.
  Definition gname : Set := mutex_gname.

  Definition mutex_inv_namespace (g : gname) : namespace :=
    g.(state_namespace).

  Lemma mutex_inv_namespace_not_root g : mutex_inv_namespace g <> nroot.
  Proof. exact g.(state_namespace_not_root). Qed.

  Canonical Structure token_cmraR : cmra := fracR.

  Class stateG `{Σ : cpp_logic} := {
    #[local] has_token_own :: HasOwn (iPropI _Σ) token_cmraR;
    #[local] has_token_upd :: HasOwnUpd (iPropI _Σ) token_cmraR;
    #[local] has_token_valid :: HasOwnValid (iPropI _Σ) token_cmraR;
    #[global] owners_G :: OwnerTid.G Σ;
  }.
  Definition G := @stateG.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.
  #[global] Instance state_G `{Σ : cpp_logic} (H : G Σ) : @stateG _ _ Σ := H.

  Definition token `{Σ : cpp_logic, !G Σ} (γ : gname) (q : cQp.t) : mpred :=
    own γ.(token_gname) (cQp.frac q : token_cmraR).

  Definition not_locked `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (γ : gname) (th : thread_idT) (q : cQp.t) : mpred :=
    own γ.(token_gname) (cQp.frac q : token_cmraR) **
    MutexSets.my_mutexes th (coPset.CoPset $ ↑mutex_inv_namespace γ).

  Definition state `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (γ : gname) (b : bool) : mpred :=
    ∃ th q,
      owner_tid_auth γ.(owner_gname) (if b then Some (th, q) else None) **
      if b then
        (* The mutex owner deposits [not_locked] and takes [owner_tid_frag],
           which records the [th] and [q] stored in the invariant. *)
        not_locked this γ th q
      else
        owner_tid_frag γ.(owner_gname) None.

  #[global] Instance state_WeaklyObjective
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this γ b :
    WeaklyObjective (state this γ b).
  Proof. rewrite /state /not_locked. destruct b; apply _. Qed.

  Section state_laws.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.

    Lemma alloc_state {σ : genv} this gi (N : namespace) (HN : N <> nroot) :
      ⊢ |==> ∃ γ, [| γ.(state_namespace) = N |] **
        token (MkGname γ gi) 1$m **
        state this (MkGname γ gi) false.
    Proof.
      iMod (own_alloc (1%Qp : token_cmraR)) as (gt) "T"; first done.
      iMod (OwnerTid.alloc None) as (go) "[OA OF]".
      iModIntro. iExists (MkStateGname gt go N HN).
      iSplit; first done.
      rewrite /token /state /=. iFrame "T".
      iExists thread_id_specs.default_thread_id, (1$m)%cQp. iFrame.
    Qed.

    Lemma state_lock {σ : genv} this (γ : gname) th (q : cQp.t) :
      state this γ false ** not_locked this γ th q |--
        (|==> state this γ true ** owner_tid_frag γ.(owner_gname) (Some (th, q))).
    Proof.
      rewrite /state.
      iIntros "[State NL]".
      iDestruct "State" as (old_th old_q) "[OA OF]".
      iMod (owner_update γ.(owner_gname) None None (Some (th, q))
        with "[$OA $OF]") as "[OA OF]".
      iModIntro. iFrame "OF". iExists th, q. iFrame.
    Qed.

    Lemma state_unlock {σ : genv} this (γ : gname) th (q : cQp.t) :
      state this γ true ** owner_tid_frag γ.(owner_gname) (Some (th, q)) |--
        (|==> state this γ false ** not_locked this γ th q).
    Proof.
      rewrite /state.
      iIntros "[State OF]".
      iDestruct "State" as (owner held_q) "[OA NL]".
      iDestruct (observe_2 [| Some (owner, held_q) = Some (th, q) |]
        with "OA OF") as %Heq.
      injection Heq as -> ->.
      iMod (owner_update γ.(owner_gname) _ _ None with "[$OA $OF]") as "[OA OF]".
      iModIntro. iFrame "NL". iExists th, q. iFrame.
    Qed.

    Lemma unlocked_owner_tid_frag {σ : genv} this γ th q :
      state this γ false ** owner_tid_frag γ.(owner_gname) (Some (th, q)) |-- False.
    Proof.
      rewrite /state. iIntros "[State OF]".
      iDestruct "State" as (old_th old_q) "[_ OF0]".
      iDestruct (owner_tid_frag_exclusive with "OF0 OF") as %[].
    Qed.

    Lemma locked_full_token {σ : genv} this γ :
      state this γ true ** token γ 1$m |-- False.
    Proof.
      rewrite /state /not_locked /token. iIntros "[State T]".
      iDestruct "State" as (th q) "(_ & Held & _)".
      iDestruct (own_valid_2 with "T Held") as %Hbad.
      iPureIntro. exact (Qp.not_add_le_l 1 (cQp.frac q) Hbad).
    Qed.
  End state_laws.

  #[global] Hint Opaque not_locked state : sl_opacity typeclass_instances.

  Definition globals `{Σ : cpp_logic} {σ : genv} (q : cQp.t) : mpred :=
    _global "std::memory_order_seq_cst" |->
      primR "enum std::memory_order" q
        (memory_order.to_val memory_order.seq_cst).

  #[global] Arguments globals /.

  Definition locked `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (γ : gname) (th : thread_idT) (q : cQp.t) : mpred :=
    this ,, _field "MyMutex::m_owner" |-> thread_id_specs.thread_idR 1$m th **
      owner_tid_frag γ.(owner_gname) (Some (th, q)).
  #[global] Hint Opaque token : sl_opacity typeclass_instances.
  #[global] Hint Opaque locked : typeclass_instances.
  #[global] Arguments locked /.

  #[global] Instance token_fractional `{Σ : cpp_logic, !G Σ} γ :
      CFractional (token γ).
  Proof.
    intros q1 q2. rewrite /token cQp.frac_add -own_op. done.
  Qed.
  #[global] Instance token_timeless `{Σ : cpp_logic, !G Σ} γ q :
      Timeless (token γ q).
  Proof. rewrite /token. apply _. Qed.
  #[global] Instance not_locked_timeless `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this γ th q : Timeless (not_locked this γ th q).
  Proof. rewrite /not_locked. apply _. Qed.
  #[global] Instance not_locked_exclusive `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this γ th : Exclusive1 (not_locked this γ th).
  Proof.
    intros q1 q2. rewrite /not_locked.
    iIntros "[_ F1] [_ F2]".
    have Hoverlap : ~ ((↑ mutex_inv_namespace γ : coPset) ## ↑ mutex_inv_namespace γ).
    { have Hnonempty := nclose_non_empty (mutex_inv_namespace γ). set_solver. }
    iDestruct (MutexSets.my_mutexes_exclusive th
      (↑ mutex_inv_namespace γ) (↑ mutex_inv_namespace γ) Hoverlap
      with "[$F1 $F2]") as %[].
  Qed.
  #[global] Instance locked_timeless `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this γ th q : Timeless (locked this γ th q).
  Proof. rewrite /locked. apply _. Qed.
  #[global] Instance locked_exclusive `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this γ : Exclusive2 (locked this γ).
  Proof. intros th1 th2 q1 q2. rewrite /locked. apply observe_2_sep_r. apply _. Qed.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
    WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.

  #[global] Instance locked_WeaklyObjective `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      this γ th q : WeaklyObjective (locked this γ th q).
  Proof. rewrite /locked. apply _. Qed.

  Section with_Σ.
    Context `{Σ : cpp_logic}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.

    (** The physical lock bit agrees with the abstract ghost state. The
        protected resources and cleared owner field are available while free. *)
    Definition mutex_inv {σ : genv} (this : ptr) (γ : gname) (P : mpred) : mpred :=
      ∃ b : bool,
      this ,, _field "MyMutex::m_lock" |->
        atomic.R "int" 1$m (if b then 1 else 0)%Z **
      state this γ b **
      if b then emp else
        P ** this ,, _field "MyMutex::m_owner" |-> thread_id_specs.thread_idR 1$m thread_id_specs.default_thread_id.

    Definition R {HAS_THREADS : HasStdThreads Σ} {σ : genv} (γ : gname) (q : cQp.t) (P : mpred) : Rep :=
      structR class_name q$m **
      as_Rep (fun this =>
        cinv (mutex_inv_namespace γ) (cinv_gname γ) (mutex_inv this γ P) **
        cinv_own (cinv_gname γ) q
      ).
    #[global] Hint Opaque R : sl_opacity typeclass_instances.
    #[only(type_ptr,cfractional,ascfractional,cfracvalid)] derive R.

    #[global] Instance R_learnable {HAS_THREADS : HasStdThreads Σ} {σ : genv} :
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

    Context {σ : genv} {HAS_THREADS : HasStdThreads Σ}.

    Lemma locked_my_mutexes_exclusive (this : ptr) g th q qt P E :
      ↑mutex_inv_namespace g ⊆ E ->
      this |-> R g q P ** locked this g th qt **
        MutexSets.my_mutexes th
          (coPset.CoPset $ ↑mutex_inv_namespace g) |-- (|={E}=> False).
    Proof.
      iIntros (Hmask) "(HR & Locked & Names)".
      iEval (rewrite /R _at_sep _at_as_Rep) in "HR".
      iDestruct "HR" as "(_ & #CI & CO)".
      iInv (mutex_inv_namespace g) as "[Inv CO]" "Hclose".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (b) "(_ & State & _)".
      iEval (rewrite /locked) in "Locked".
      iDestruct "Locked" as "[_ OF]".
      iEval (rewrite /state /not_locked) in "State".
      destruct b.
      - iDestruct "State" as (owner held_q) "(>OA & _ & >Sets)".
        iDestruct (observe_2 [| Some (owner, held_q) = Some (th, qt) |]
          with "OA OF") as %Heq.
        injection Heq as -> ->.
        iDestruct (MutexSets.my_mutexes_exclusive with "[$Sets $Names]") as %[].
        rewrite /mutex_inv_namespace.
        have Hnonempty := nclose_non_empty g.(state_namespace).
        set_solver.
      - iDestruct "State" as (owner held_q) "[_ >OF0]".
        iDestruct (owner_tid_frag_exclusive with "OF0 OF") as %[].
    Qed.

    #[global] Instance locked_learn :
        Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> req_eq ==> learn_hints.fin) locked).
    Proof using MUTEX_SETS. solve_learnable. Qed.

    Definition do_lock (this : ptr) (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ thr qt, current_thread thr ** not_locked this lk.1 thr qt **
        (locked this lk.1 thr qt ** lk.2 -* K).
    #[global] Arguments do_lock /.

    Definition do_unlock (this : ptr) (lk : gname * mpred) (K : mpred) : mpred :=
      ∃ thr qt, current_thread thr ** locked this lk.1 thr qt ** ▷lk.2 **
        (not_locked this lk.1 thr qt -* K).
    #[global] Arguments do_unlock /.

    #[global] Instance mutex_basic_lockable :
        BasicLockable (T := gname * mpred) cpp_ty
          (fun q gP => R gP.1 q gP.2) :=
      { do_lock := do_lock
      ; do_unlock := do_unlock }.

    Definition do_try_lock (this : ptr) (lk : gname * mpred)
        (K : bool -> mpred) : mpred :=
      ∃ thr qt, current_thread thr ** not_locked this lk.1 thr qt **
        ∀ b : bool,
          (if b then lk.2 ** locked this lk.1 thr qt
            else not_locked this lk.1 thr qt) -* K b.
    #[global] Arguments do_try_lock /.

    #[global] Instance mutex_lockable :
        Lockable (T := gname * mpred) cpp_ty
          (fun q gP => R gP.1 q gP.2) :=
      { do_try_lock := do_try_lock }.

    Lemma init_R (this : ptr) (old : gname)
        (N : namespace) (P : mpred) :
      WeaklyObjective P ->
      N <> nroot ->
      this |-> R old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g, [| mutex_inv_namespace g = N |] **
          this |-> R g 1$m P ** token g 1$m).
    Proof.
      intros HP HN. iIntros "(HR & T & P)".
      iEval (rewrite /R _at_sep _at_as_Rep) in "HR".
      iDestruct "HR" as "(S & #CI & CO)".
      iMod (cinv_cancel with "CI CO") as "Inv"; [done..|].
      iMod (cinv_alloc_cofinite ∅ ⊤ N) as (gi) "(_ & COnew & Alloc)".
      iMod (alloc_state this gi N HN) as (gs) "(%Hnamespace & Tnew & Stnew)".
      iMod ("Alloc" $! (mutex_inv this (MkGname gs gi) P)
        with "[] [Inv P Stnew T]") as "#CInew".
      { iPureIntro. apply _. }
      { iNext. rewrite /mutex_inv.
        iDestruct "Inv" as (b) "(L & St & Resources)".
        destruct b.
        - iDestruct (locked_full_token with "[$St $T]") as %[].
        - iDestruct "Resources" as "[_ Owner]".
          iExists false. iFrame "L Stnew P Owner".
          iApply (affine with "[St T]"); last iAccu. apply mpred_BiAffine. }
      iModIntro. iExists (MkGname gs gi).
      iSplit; first (iPureIntro; exact Hnamespace).
      rewrite /R _at_sep _at_as_Rep /mutex_inv_namespace /= Hnamespace.
      iFrame "CInew S COnew Tnew".
    Qed.

  End with_Σ.
End CustomMutexPreds.

(** Verify the implementation using its ghost resources and public state predicates. *)
Module custom_mutex.
  Import CustomMutexPreds.
  Module Spec := mutex_spec CustomMutexPreds.

  Abbreviation N := "MyMutex"%cpp_name.
  #[local] Hint Opaque thread_id_specs.thread_idR : sl_opacity typeclass_instances.

  #[local] Instance at_WeaklyObjective `{Σ : cpp_logic}
      (p : ptr) (R : Rep) `{!WeaklyObjective (R p)} :
    WeaklyObjective (p |-> R).
  Proof. rewrite INTERNAL._at_eq. apply _. Qed.

  Abbreviation IR := CustomMutexPreds.R.

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, HAS_THREADS : !HasStdThreads Σ}.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!CustomMutexPreds.G Σ}.

    Context `{MOD : source ⊧ σ}.

    (* FIXME any reason to keep Reduce? *)
    cpp.spec "MyMutex::MyMutex()" as ctor_spec with
      (\exact Reduce (Spec.ctor_spec)).

    cpp.spec "MyMutex::~MyMutex()" as dtor_spec with
      (\exact Reduce (Spec.dtor_spec)).

    Definition T : Type := gname * mpred.
    cpp.spec "MyMutex::do_lock()" as do_lock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \prepost{qg} globals qg
      \pre{qt} not_locked this g thr qt
      \post P **
        this ,, _field "MyMutex::m_owner" |-> thread_id_specs.thread_idR 1$m thread_id_specs.default_thread_id **
        owner_tid_frag g.(owner_gname) (Some (thr, qt))).

    cpp.spec "MyMutex::do_unlock()" as do_unlock_spec with (
      \this this
      \prepost{g q P} this |-> IR g q P
      \persist{thr} current_thread thr
      \prepost{qg} globals qg
      \pre{(qt : cQp.t)} this ,, _field "MyMutex::m_owner" |-> thread_id_specs.thread_idR 1$m thread_id_specs.default_thread_id **
        owner_tid_frag g.(owner_gname) (Some (thr, qt))
      \pre ▷P
      \post not_locked this g thr qt).

    cpp.spec "MyMutex::lock()" as lock_spec_alt with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.lock_spec_alt this)).

    cpp.spec "MyMutex::unlock()" as unlock_spec_alt with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.unlock_spec_alt this)).

    cpp.spec "MyMutex::lock()" as lock_spec with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce
        (Spec.lock_spec this)).

    cpp.spec "MyMutex::unlock()" as unlock_spec with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce
        (Spec.unlock_spec this)).

    cpp.spec "MyMutex::try_lock()" as try_lock_spec_alt with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.try_lock_spec_alt this)).

    cpp.spec "MyMutex::try_lock()" as try_lock_spec with
      (\this this
       \prepost{qg} globals qg
       \exact Reduce (Spec.try_lock_spec this)).

    Lemma try_lock_spec_equiv_try_lock_spec_alt : try_lock_spec ⊣⊢ try_lock_spec_alt.
    Proof.
      rewrite /try_lock_spec /try_lock_spec_alt /specify.
      do 2 f_equiv. intros this xs K.
      rewrite !add_with_equiv. f_equiv=> qg.
      rewrite !add_prepost_equiv Spec.try_lock_spec_equiv_try_lock_spec_alt; done.
    Qed.

    Lemma lock_spec_equiv_lock_spec_alt : lock_spec ⊣⊢ lock_spec_alt.
    Proof.
      rewrite /lock_spec /lock_spec_alt /specify.
      do 2 f_equiv. intros this xs K.
      rewrite !add_with_equiv.
      f_equiv=> qg.
      by rewrite !add_prepost_equiv Spec.lock_spec_equiv_lock_spec_alt.
    Qed.

    Lemma unlock_spec_equiv_unlock_spec_alt : unlock_spec ⊣⊢ unlock_spec_alt.
    Proof.
      rewrite /unlock_spec /unlock_spec_alt /specify.
      do 2 f_equiv. intros this xs K.
      rewrite !add_with_equiv.
      f_equiv=> qg.
      by rewrite !add_prepost_equiv Spec.unlock_spec_equiv_unlock_spec_alt.
    Qed.

    Abbreviation BASE p := (p ,, _base "std::atomic<int>" "std::__atomic_base<int>").

    Definition bi_later_exist_F := [FWD] @bi.later_exist.
    Definition bi_later_sep_F := [FWD] @bi.later_sep.
    Hint Resolve bi_later_exist_F bi_later_sep_F : br_hints.

    #[program]
    Definition do_exchange_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming{qt} not_locked p g thr qt
      \proving{K (_ : IsExistential K)}
      std.atomic.do_exchange "int" (BASE (p,, o_field σ "MyMutex::m_lock") ) 1%Z K
      \instantiate K := (fun res => p |-> IR g q P ** [| res = 0 \/ res = 1 |]%Z **
                          if bool_decide (res = 0) then P ** owner_tid_frag g.(owner_gname) (Some (thr, qt)) **
                            p ,, _field "MyMutex::m_owner" |-> thread_id_specs.thread_idR 1$m thread_id_specs.default_thread_id
                          else not_locked p g thr qt)
                          \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & NL)".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_exchange.
      iAuIntro1. rewrite /atomic1_acc.
      iInv (mutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (b) "(>L & State & Resources)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if b then 1 else 0)%Z.
      iSplitL "L".
      { ework $usenamed=true with br_erefl. }
      iSplit.
      - iIntros "L". iMod "Y" as "_".
        iMod ("Hclose" with "[L State Resources]") as "_".
        { iNext. rewrite /mutex_inv. iExists b.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro. iFrame.
      - iNext. iIntros "L". iMod "Y" as "_".
        destruct b.
        + iMod ("Hclose" with "[L State Resources]") as "_".
          { iNext. rewrite /mutex_inv. iExists true.
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iFrame. }
          iModIntro. rewrite /IR _at_sep _at_as_Rep /=.
          iFrame "CI". iFrame. iPureIntro. auto.
        + iDestruct "Resources" as "[P Owner]".
          iMod (state_lock p _ with "[$State $NL]") as "[State Locked]".
          iMod ("Hclose" with "[L State]") as "_".
          { iNext. rewrite /mutex_inv. iExists true.
            iSplitL "L"; first by ework $usenamed=true with br_erefl.
            iFrame. }
          iModIntro. rewrite /IR _at_sep _at_as_Rep /=.
          iFrame "CI". iFrame. iPureIntro. auto.
    Qed.
    Hint Resolve do_exchange_C : sl_opacity.

    #[program]
    Definition do_store_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \using{thr} current_thread thr
      \consuming{g q P} p |-> IR g q P
      \consuming P
      \consuming p ,, _field "MyMutex::m_owner" |-> thread_id_specs.thread_idR 1$m thread_id_specs.default_thread_id
      \consuming{(qt : cQp.t)} owner_tid_frag g.(owner_gname) (Some (thr, qt))
      \proving{K (_ : IsExistential K)}
        std.atomic.do_store "int" (BASE (p ,, o_field σ "MyMutex::m_lock")) 0%Z K
      \instantiate K := (p |-> IR g q P ** not_locked p g thr qt)
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M Hpre]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      iDestruct "Hpre" as "(#Thr & IR & P & Owner & Locked)".
      iEval (rewrite /IR _at_sep _at_as_Rep) in "IR".
      iDestruct "IR" as "(S & #CI & CO)".
      rewrite /std.atomic.do_store.
      iAcIntro. rewrite /commit_acc /=.
      iInv (mutex_inv_namespace g) as "Inv" "Hclose".
      iDestruct "Inv" as "[Inv CO]".
      iEval (rewrite /mutex_inv) in "Inv".
      iDestruct "Inv" as (b) "(>L & State & Resources)".
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; first set_solver.
      iExists (if b then 1 else 0)%Z.
      iSplitL "L"; first by ework $usenamed=true with br_erefl.
      iNext. iIntros "L". iMod "Y" as "_".
      destruct b.
      - iMod (state_unlock p _ with "[$State $Locked]") as "[State NL]".
        iMod ("Hclose" with "[L State P Owner]") as "_".
        { iNext. rewrite /mutex_inv. iExists false.
          iSplitL "L"; first by ework $usenamed=true with br_erefl.
          iFrame. }
        iModIntro.
        rewrite /IR _at_sep _at_as_Rep /=.
        iFrame "CI". iFrame.
      - iDestruct (unlocked_owner_tid_frag with "[$State $Locked]") as %[].
    Qed.
    Hint Resolve do_store_C : sl_opacity.

    #[program]
    Definition do_load_C (p : ptr) :=
      \cancelx
      \using denoteModule source
      \consuming{q (n : Z)} p |-> atomic.R "int" q n
      \proving{(K : Z -> mpred) (_ : IsExistential K)}
        std.atomic.do_load "int" (BASE p) K
      \instantiate K :=
        (fun x : Z => p |-> atomic.R "int" q n ** [| x = n |])
      \end@{mpredI}.
    Next Obligation.
      intros. iIntros "[#M ?]" (?? ->).
      iDestruct (observe [| _ ⊧ _ |] with "M") as "%".
      rewrite /std.atomic.do_load.
      iAcIntro. rewrite /commit_acc.
      iDestruct (fupd_mask_subseteq) as ">Y"; [ | iModIntro ]; eauto.
      work. iExists q. work.
      iMod "Y". iModIntro.
      work.
    Qed.
    Hint Resolve do_load_C : sl_opacity.

    Lemma mymutex_do_lock_proof : verify[source] "MyMutex::do_lock()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wp_while (fun _ => emp); go; first by ework.
      wp_if; go.
    Qed.

    Lemma mymutex_do_unlock_proof : verify[source] "MyMutex::do_unlock()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
    Qed.

    #[local] Remove Hints CustomMutexPreds.locked_learn : typeclass_instances.

    Lemma mymutex_lock_alt_proof : verify[source] lock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
      wname [CustomMutexPreds.not_locked] "NL".
      iFrame "NL". ego.
      Unshelve. all: exact (1$m)%cQp.
    Qed.

    Lemma mymutex_try_lock_alt_proof : verify[source] try_lock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec; ego.
      repeat (first [case_bool_decide | wp_if]; ego).
    Qed.

    Lemma mymutex_try_lock_proof : verify[source] try_lock_spec.
    Proof using MOD HAS_THREADS.
      rewrite try_lock_spec_equiv_try_lock_spec_alt.
      exact mymutex_try_lock_alt_proof.
    Qed.

    Lemma mymutex_unlock_alt_proof : verify[source] unlock_spec_alt.
    Proof using MOD HAS_THREADS.
      verify_spec.
      repeat (go; ework).
      wname [owner_tid_frag] "Owner".
      iFrame "Owner". ego.
      Unshelve. all: exact (1$m)%cQp.
    Qed.

    Lemma mymutex_ctor_proof : verify[source] "MyMutex::MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec; go.
      wname [structR] "S".
      wname [P] "P".
      wname [_ |-> atomic.R _ _ _] "L".
      wname [_ |-> thread_id_specs.thread_idR _ _] "Owner".
      iMod (cinv_alloc_cofinite ∅ ⊤ N) as (gi) "(_ & CO & Alloc)".
      iMod (alloc_state this gi N ltac:(done)) as (gs) "(%Hnamespace & T & State)".
      iMod ("Alloc" $! (mutex_inv this (MkGname gs gi) P)
        with "[] [L P Owner State]") as "#CI".
      { iPureIntro. apply _. }
      { iNext. rewrite /mutex_inv. iExists false. iFrame. }
      iModIntro. iExists (MkGname gs gi).
      iSplit; first (iPureIntro; exact Hnamespace).
      rewrite /IR _at_sep _at_as_Rep /mutex_inv_namespace /= Hnamespace.
      iFrame "CI". iFrame.
    Qed.

    Lemma mymutex_dtor_proof : verify[source] "MyMutex::~MyMutex()".
    Proof using MOD HAS_THREADS.
      verify_spec.
      rewrite /IR /mutex_inv.
      work.
      wname [cinv] "#CI".
      wname [cinv_own] "CO".
      wname [CustomMutexPreds.token] "T".
      iMod (cinv_cancel with "CI CO")
        as "Inv"; [done..|].
      go.
      iDestruct "Inv" as (b) "(Lock & State & Resources)".
      destruct b.
      - iDestruct (locked_full_token with "[$State $T]") as %[].
      - iDestruct "Resources" as "[P Owner]".
        iAssert emp with "[State T]" as "_".
        { iApply (affine with "[State T]"); last iAccu. apply mpred_BiAffine. }
        ego $usenamed=true with br_erefl.
    Qed.

    Lemma mymutex_lock_proof : verify[source] lock_spec.
    Proof using MOD HAS_THREADS.
      rewrite lock_spec_equiv_lock_spec_alt.
      exact mymutex_lock_alt_proof.
    Qed.

    Lemma mymutex_unlock_proof : verify[source] unlock_spec.
    Proof using MOD HAS_THREADS.
      rewrite unlock_spec_equiv_unlock_spec_alt.
      exact mymutex_unlock_alt_proof.
    Qed.

  End with_Σ.
End custom_mutex.
