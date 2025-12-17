Require Import bluerock.bi.tls_modalities.
Require Import bluerock.bi.tls_modalities_rep.
Require Import bluerock.bi.weakly_objective.
Require Import bluerock.auto.cpp.weakly_local_with.

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.brick.libstdcpp.mutex.inc_hpp.
Require Export bluerock.brick.libstdcpp.runtime.pred.

Module mutex.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive R.
  (*
  #[global] Declare Instance mutex_rep_typed : Typed3 "std::mutex" mutex_rep.
  #[global] Declare Instance mutex_rep_cfrac : forall γ, CFractional1 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_ascfrac : forall γ, AsCFractional2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_cfracvalid : forall γ, CFracValid2 (mutex_rep γ).
  #[global] Declare Instance mutex_rep_timeless : Timeless3 mutex_rep.
  *)
  #[global] Declare Instance mutex_rep_typed : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, Typed3 "std::mutex" R.

  (* TODO: index this by the specific mutex! Either via a mutex_gname or by making this a Rep *)
  (* TODO: why is this separate from [mutex_rep] *)
  Parameter mutex_token : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred.
  #[only(cfractional,cfracvalid,ascfractional,timeless)] derive mutex_token.
  (*
  #[global] Declare Instance mutex_token_cfrac : CFractional1 mutex_token.
  #[global] Declare Instance mutex_token_ascfrac : AsCFractional1 mutex_token.
  #[global] Declare Instance mutex_token_cfracvalid : CFracValid1 mutex_token.
  #[global] Declare Instance mutex_token_timeless : Timeless2 mutex_token.
  *)
  #[global] Declare Instance mutex_rep_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).


  (** A resource enforcing that the thread calling unlock must be the same thread
      that owns the lock

  TODO: maybe a bigger test demonstrating the enforcement?
  minimal version: this fails (fill in the obvious stuff)

    \persist{th} >={ L_TI } th
    \pre{j} mutex_locked g j
    test_unlock(std::mutex & m) {
      m.unlock();
    }

    this succeeds:

    \persist{th} >={ L_TI } th
    \pre mutex_locked g th
    same test_unlock
   *)
  Parameter mutex_locked : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> thread_idT -> mpred.
  #[only(timeless,exclusive)] derive mutex_locked.
  (*
  Declare Instance mutex_locked_timeless : Timeless2 mutex_locked.
  Declare Instance mutex_locked_excl g : Exclusive1 (mutex_locked g).
  *)

  Context `{MOD : inc_hpp.source ⊧ σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec "std::mutex::mutex()" as ctor_spec with
      (\this this
      \pre{P} ▷P
      \post Exists g, this |-> R g 1$m P ** mutex_token g 1$m).

  cpp.spec "std::mutex::lock()" as lock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_token g q
      \post P ** mutex_locked g thr).

  cpp.spec "std::mutex::try_lock()" as try_lock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \prepost{th} current_thread th
      \pre mutex_token g q
      \post{b}[Vbool b] if b then P ** mutex_locked g th else mutex_token g q).

  cpp.spec "std::mutex::unlock()" as unlock_spec with
      (\this this
      \prepost{q P g} this |-> R g q P (* part of both pre and post *)
      \persist{thr} current_thread thr
      \pre mutex_locked g thr
      \pre ▷P
      \post mutex_token g q).

  cpp.spec "std::mutex::~mutex()" as dtor_spec with
      (\this this
      \pre{g P} this |-> R g 1$m P ** mutex_token g 1$m
      \post P).

End with_cpp.
End mutex.

(* TODO upstream *)
#[global] Declare Instance
  own_WeaklyObjective `{Σ : cpp_logic} {A : cmra} `{!HasOwn mpredI A} γ (a : A)  :
  WeaklyObjective (PROP := iPropI _) (own γ a).

Module recursive_mutex.

  (** <<locked γ th n>> <<th>> owns the mutex <<γ>> <<n>> times. *)
  Parameter locked : ∀ `{Σ : cpp_logic}, gname -> thread_idT -> nat -> mpred.
  #[global] Declare Instance
    locked_WeaklyObjective `{Σ : cpp_logic} γ thr n :
    WeaklyObjective (PROP := iPropI _) (locked γ thr n).

  (* the mask of recursive_mutex *)
  Definition mask := nroot .@@ "std" .@@ "recursive_mutex".

  (** Derived construction *)
  Record rmutex_gname :=
    { lock_gname : gname; level_gname : gname }.
  Definition rmutex_namespace := nroot .@@ "std" .@@ "recursive_mutex_inv".

  Canonical Structure cmraR := (excl_authR (prodO natO thread_idTO)).

  br.lock
  Definition inv_rmutex `{Σ : cpp_logic} `{!HasOwn mpredI cmraR} (g : rmutex_gname) (P : mpred) : mpred :=
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

  Parameter used_threads : ∀ `{Σ : cpp_logic}, gname -> gset thread_idT -> mpred.

  br.lock
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

  br.lock
  Definition release {TT} (a : acquire_state TT) : acquire_state TT :=
    match a with
    | NotHeld => NotHeld (* unreachable *)
    | Held n xs =>
        match n with
        | 0 => NotHeld
        | S n => Held n xs
        end
    end.

  br.lock
  Definition acquireable `{Σ : cpp_logic, !HasStdThreads Σ, !HasOwn mpredI cmraR} (g : rmutex_gname) (th : thread_idT) {TT: tele} (t : acquire_state TT) (P : TT -t> mpred) : mpred :=
    current_thread th **
    match t with
    | NotHeld => locked g.(lock_gname) th 0
    | Held n args => own g.(level_gname) (◯E (S n, th)) ** tele_app P args
    end.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    #[global] Declare Instance locked_timeless : Timeless3 locked.
    Axiom locked_excl_same_thread : forall g th n m,
      locked g th n ** locked g th m |-- False.
    Axiom locked_excl_different_thread : forall g th th' n m,
      locked g th n ** locked g th' m |-- [| n = 0 \/ m = 0 |] ** True.

    Context `{!HasOwn mpredI cmraR, !HasStdThreads Σ}.

    #[global] Instance acquireable_learn γ th TT : LearnEq2 (acquireable γ th (TT := TT)).
    Proof. solve_learnable. Qed.

    #[global] Instance acquireable_current_thread :
      `{Observe (current_thread th) (acquireable g th (TT := TT) t P)}.
    Proof. rewrite acquireable.unlock; apply _. Qed.

    Axiom use_thread : forall th g m,
      th ∉ m ->
      current_thread th ** used_threads g m |-- |==> used_threads g (m ∪ {[ th ]}) ** locked g th 0.

    Lemma use_thread_acquirable {TT} th g m P :
      th ∉ m ->
      current_thread th ** used_threads g.(lock_gname) m |-- |==>
      used_threads g.(lock_gname) (m ∪ {[ th ]}) ** acquireable (TT := TT) g th NotHeld P.
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

  (* NOTE: Invariant used to protect resource [r]
    inv (r \\// exists th n, locked th (S n)) *)

  (* recursive mutex -- ownership of the class. *)
  Parameter R : gname -> cQp.t -> Rep.
  #[only(cfractional,ascfractional,timeless,type_ptr="std::recursive_mutex")] derive R.
  #[global] Instance R_learn : Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) R).
  Proof. solve_learnable. Qed.

  (* #[only(cfractional,timeless)] derive mutex_rep. *)
  (** <<token γ q>> if <<q = 1>>, then the mutex is not locked and therefore can be destroyed.
      <<token γ 1>> is shared among threads who has access to the lock, and a call to lock
      turns some of <<token γ q>> into <<given_token γ q>>, unlock does the opposite.
  *)

  Parameter token : gname -> cQp.t -> mpred.
  #[only(cfracsplittable,timeless)] derive token.
  Parameter given_token : gname -> cQp.t -> mpred.
  #[only(timeless)] derive given_token.

  #[global]
  Instance given_token_learn γ : LearnEq1 (given_token γ) :=
    ltac:(solve_learnable).

  (* #[only(cfracsplittable,timeless)] derive given_token. *)

  cpp.spec "std::recursive_mutex::recursive_mutex()" as ctor_spec with
    (\this this
     \post Exists g, this |-> R g 1$m ** token g 1 ** used_threads g empty).

  cpp.spec "std::recursive_mutex::~recursive_mutex()" as dtor_spec with
    (\this this
     \pre{g} this |-> R g 1$m
     \pre token g 1
     \pre{ths} used_threads g ths
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


  (* Alternative style:
      R γ q r ** locked γ th (S n) |--| R γ q r ** r ** was_locked γ th (S n)

      possible solution: two specs/choice in the spec for unlock: either
      {locked γ th (n+1)} unlock() {locked γ th n}
      or
      {was_locked γ th (n+2)} unlock() {locked γ th (n+1)}
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

  Context `{!HasOwn mpredI cmraR}.

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
  Definition own_P_is_acquireable_C {TT} g n P args :=
    \cancelx
    \preserving{th} current_thread th
    \consuming own g.(level_gname) (◯E (S n, th))
    \through tele_app P args
    \proving acquireable (TT := TT) g th (Held n args) P
    \end.
  Next Obligation. rewrite acquireable.unlock; work. Qed.

  #[global] Instance : `{Learnable
    (current_thread th)
    (acquireable (TT := TT0) γ th0 args P0)
    [th0 = th] }.
  Proof. solve_learnable. Qed.

  #[global] Instance : `{Learnable
    (inv_rmutex γ1 P1)
    (inv_rmutex γ2 P2)
    [γ2 = γ1] }.
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

  (* TODO maybe a hint that says
    TCEq f1 f2 ->
    acquireable _ _ f1 ⊢ acquireable _ _ f2.
    *)
  Lemma update_eq {TT : tele} f t1 t2 : acquire t1 t2 ->
      update f t1 = release (TT := TT) (update f t2).
  Proof.
    by intros ([|] & ? & -> & ->)%is_held; rewrite !release.unlock.
  Qed.

  (* this is the usable pre-condition *)
  cpp.spec "std::recursive_mutex::recursive_mutex()" as ctor_spec' with
    (\this this
     \persist{th} current_thread th
     \pre{TT P xs} tele_app (TT := TT) P xs
     \require ∀ xs, WeaklyObjective (tele_app P xs)
     \post
      Exists g,
        this |-> R g.(lock_gname) 1 **
        token g.(lock_gname) 1$m **
        used_threads g.(lock_gname) empty **
        inv_rmutex g (∃ xs, tele_app P xs)).

  cpp.spec "std::recursive_mutex::lock()" as lock_spec' with
    (\this this
     \persist{g TT P} inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
     \prepost{q} this |-> R g.(lock_gname) q
     \pre{th n} acquireable g th n P
     \pre{q'} token g.(lock_gname) q'
     \post given_token g.(lock_gname) q' ** Exists n', [| acquire n n' |] ** ▷ acquireable g th n' P).
  (* to prove: this is derivable from lock_spec *)

  cpp.spec "std::recursive_mutex::unlock()" as unlock_spec' with
    (\this this
     \persist{g TT P} inv_rmutex g (∃ xs, tele_app (TT := TT) P xs)
     \prepost{q} this |-> R g.(lock_gname) q
     \pre{th n args} acquireable g th (Held n args) P
     \pre{q'} given_token g.(lock_gname) q'
     \post token g.(lock_gname) q' ** ▷ acquireable g th (release $ Held n args) P).

  Definition acquireable_current_thread_F :=
    ltac:(mk_obs_fwd acquireable_current_thread).
  #[local] Hint Resolve acquireable_current_thread_F : br_hints.

  (* TODO AUTO *)
  #[global] Instance later_acquireable_learn γ th TT :
    LearnEq2 (fun a b => bi_later (acquireable γ th (TT := TT) a b)).
  Proof. solve_learnable. Qed.

  (* #[global] Instance token_learn γ :
    LearnEq1 (token γ).
  Proof. solve_learnable. Qed. *)

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

  Lemma lock_spec_impl_lock_spec' :
    lock_spec |-- lock_spec'.
  Proof using MOD HOV HOU.
    apply specify_mono; work.

    iExists _, q', (∃ t : acquire_state TT, [| acquire n t |] ∗
              ▷ acquireable g th t P)%I.
    work.

    wname [bi_wand] "W".
    wfocus (bi_wand _ _) "W".
    { work $usenamed=true. }
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
      wname [locked _ th _] "Hlocked".
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
      wname [locked _ th _] "Hlocked".
      iMod ("Hclose" with "[$Hg $Hlocked //]") as "_".
      iModIntro.
      iExists (Held (S n) xs). work $usenamed=true.
  Qed.

  Lemma unlock_spec_impl_unlock_spec' :
    unlock_spec |-- unlock_spec'.
  Proof using MOD HOV HOU.
    apply specify_mono; work.
    iExists _, (▷ acquireable g th (release $ Held n args) P)%I.
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
