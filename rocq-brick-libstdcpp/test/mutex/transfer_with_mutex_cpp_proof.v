Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.test.mutex.transfer_with_mutex_cpp.

Import linearity.

(** std::lock_guard<std::recursive_mutex> specs.
    TODO remove this when lock_guard<BasicLockable T> works. *)
Module transfer_lock_guard.

sl.lock
Definition R `{Σ : cpp_logic, σ : genv, !std_recursive_mutex.G Σ, !HasStdThreads Σ}
    (mp : ptr) (g : std_recursive_mutex.gname) (q : cQp.t) (P : mpred) : Rep :=
  structR "std::lock_guard<std::recursive_mutex>" 1$m **
  _field "std::lock_guard<std::recursive_mutex>::_M_device"
    |-> refR<"std::recursive_mutex"> 1$m mp **
  pureR (mp |-> std_recursive_mutex.R g q P).
#[only(type_ptr)] derive R.
#[only(lazy_unfold)] derive R.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!std_recursive_mutex.G Σ}.

  #[local] Hint Opaque std_recursive_mutex.do_lock std_recursive_mutex.do_unlock : sl_opacity.

  #[global] Instance R_learn :
    Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).
  Proof. solve_learnable. Qed.

  cpp.spec "std::lock_guard<std::recursive_mutex>::lock_guard(std::recursive_mutex&)"
      as ctor_spec from source with (
    \this this
    \arg{mp} "m" (Vptr mp)
    \pre{g q P} mp |-> std_recursive_mutex.R g q P
    \pre{K} std_recursive_mutex.do_lock (g, P) K
    \post this |-> R mp g q P ** K
  ).

  cpp.spec "std::lock_guard<std::recursive_mutex>::~lock_guard()"
      as dtor_spec from source with (
    \this this
    \pre{mp g q P} this |-> R mp g q P
    \pre{K} std_recursive_mutex.do_unlock (g, P) K
    \post mp |-> std_recursive_mutex.R g q P ** K
  ).

  Lemma ctor_ok : verify[source] ctor_spec.
  Proof. verify_spec; go. iExists (std_recursive_mutex.Held n args). go. Qed.

  Lemma dtor_ok : verify[source] dtor_spec.
  Proof. verify_spec. rewrite !R.unlock. go. Qed.
End with_cpp.

End transfer_lock_guard.

Definition balance_args : tele := [tele (_ : Z)].
Definition balance_arg (n : Z) : balance_args :=
  {| tele_arg_head := n; tele_arg_tail := () |}.

(* sequential ownership of balance *)
sl.lock
Definition account_balanceR `{Σ : cpp_logic, σ : genv} (n : Z) : Rep :=
  _field "C::balance" |-> ulongR 1$m n.
#[only(lazy_unfold(export),timeless)] derive account_balanceR.

(* ownership of [this->mutex] and balanceR proctected by the mutex *)
sl.lock
Definition account_mutexR
    `{Σ : cpp_logic, σ : genv, !std_recursive_mutex.G Σ, !HasStdThreads Σ}
    (g : std_recursive_mutex.gname) (q : cQp.t) : Rep :=
  structR "C" q **
  as_Rep (fun this : ptr =>
    this ,, _field "C::mut" |-> std_recursive_mutex.R g q
      (∃ args : balance_args,
        tele_app (TT := balance_args) (fun n : Z => this |-> account_balanceR n) args)).
#[only(cfractional,ascfractional,type_ptr,lazy_unfold(export))] derive account_mutexR.

(** The account rep. Everything that the constructor of [C] returns.
    The recursive mutex ctor can allocate a [cinv] assocaited with any given 
    [N : namespace], and returns (most of) account_mutexR. *)
sl.lock
Definition accountR
    `{Σ : cpp_logic, σ : genv, !std_recursive_mutex.G Σ, !HasStdThreads Σ}
    (gpool : iprop.gname) (N : namespace) (q : cQp.t) : Rep :=
  Exists g,
    account_mutexR g q ** pureR (std_recursive_mutex.token g q) **
    pureR [| std_recursive_mutex.pool_name g = gpool /\
              std_recursive_mutex.rmutex_inv_namespace g = N |].
#[only(type_ptr="C")] derive accountR.

(** The two account mutexes use distinct namespaces. *)
Definition from_namespace : namespace := nroot .@@ "transfer" .@ "from".
Definition to_namespace : namespace := nroot .@@ "transfer" .@ "to".

Lemma transfer_namespaces_disjoint : (↑from_namespace : coPset) ## ↑to_namespace.
Proof. rewrite /from_namespace /to_namespace. solve_ndisj. Qed.

(** Names of the two closure types and their instantiated [C::call] methods. *)
Definition outer_lambda : name :=
  Nscoped "transfer(C&, C&, unsigned long)" (Nanon 0).
Definition lambda_call (cl : name) : name :=
  Nscoped cl (Nop function_qualifiers.Nc OOCall [Tref Tulong]).
Definition inner_lambda : name := Nscoped (lambda_call outer_lambda) (Nanon 0).
Definition account_call (cl : name) : name :=
  Ninst (Nscoped "C" (Nfunction function_qualifiers.N "call" [Tnamed cl]))
    [Atype (Tnamed cl)].

Section class_C.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!std_recursive_mutex.G Σ}.

  #[local] Instance balanceR_learn : LearnEq2 account_balanceR.
  Proof. solve_learnable. Qed.
  #[local] Instance account_mutexR_learn :
    Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) account_mutexR).
  Proof. solve_learnable. Qed.

  #[program] Definition learn_balance_args_C (P : balance_args -t> mpred) :=
    \cancelx
    \bound_existential args
    \proving tele_app P args
    \exist n
    \instantiate args := balance_arg n
    \through tele_app P (balance_arg n)
    \end.
  Next Obligation. work. Qed.
  #[local] Hint Resolve learn_balance_args_C : br_hints.

  (** calls [f], gets post condition [Q], and change that to the desired post
      condition [K]. *)
  Definition balance_callback (cl : name) (f balance : ptr) (K : mpred) : mpred :=
    ∀ Q : mpred, (K -* Q) -*
      wp_minvoke_O source Direct (Qconst (Tnamed cl)) Tvoid
        (Tfunction (FunctionType Tvoid [Tref Tulong]))
        (lambda_call cl) f [Unmaterialized (Tref Tulong) (Vptr balance)] None
        (fun _ => Q).

  #[local] Hint Opaque balance_callback std_recursive_mutex.do_lock
    std_recursive_mutex.do_unlock : sl_opacity.

  (* The internal call spec exposes the lock handle, which is supposed to be 
     hidden to the client of [C]. We define [call_spec_body] later to hide
     that. *)
  Definition account_call_internal_body (cl : name) : ptr -> WpSpec mpred val val :=
    (\this this
     \arg{f} "f" (Vptr f)
     \persist type_ptr (Tnamed cl) f
     \prepost{g q} this |-> account_mutexR g q
     \pre{K} std_recursive_mutex.do_lock
       (g, (∃ args : balance_args,
         tele_app (TT := balance_args) (fun n : Z => this |-> account_balanceR n) args)%I)
       (|={⊤}=> balance_callback cl f (this ,, _field "C::balance")
         (std_recursive_mutex.do_unlock
           (g, (∃ args : balance_args,
             tele_app (TT := balance_args) (fun n : Z => this |-> account_balanceR n) args)%I) K))
     \post K).

  cpp.spec (account_call outer_lambda) as outer_call_internal_spec from source with
    (\exact Reduce (account_call_internal_body outer_lambda)).
  cpp.spec (account_call inner_lambda) as inner_call_internal_spec from source with
    (\exact Reduce (account_call_internal_body inner_lambda)).

  (** The callback invocation is supplied by the precondition, so verification
      does not need a separate global specification for its operator(). *)
  Ltac prove_account_call :=
    verify_spec; go;
    lazymatch goal with q : cQp.t, qt : cQp.t, K : mpred |- _ =>
      iExists q, _; go;
      wname [bi_wand] "Hcallback";
      iSplitL "Hcallback"; [iExact "Hcallback"|];
      let rec open_callback :=
        first [wname [balance_callback] "Hcallback";
               iMod "Hcallback" as "Hcallback"
              | progress go1; open_callback] in
      open_callback; go;
      iEval (rewrite /balance_callback) in "Hcallback";
      iApply ("Hcallback" with "[-]"); go;
      iExists q, K; go
    end.

  Lemma outer_call_internal_ok : verify?[source] outer_call_internal_spec.
  Proof. prove_account_call. Qed.

  Lemma inner_call_internal_ok : verify?[source] inner_call_internal_spec.
  Proof. prove_account_call. Qed.

  (** call() is a wrapper for function [f] that takes the sequential ownership
      of the balance and returns an updated one. *)
  Definition call_spec_body (cl : name) : ptr -> WpSpec mpred val val :=
    (\this this
     \arg{f} "f" (Vptr f)
     \persist type_ptr (Tnamed cl) f
     \persist{th} current_thread th
     \prepost{gpool N q} this |-> accountR gpool N q **
       MutexSets.my_mutexes gpool th (coPset.CoPset (↑N))
     \pre{K} ∀ v : Z,
       this |-> account_balanceR v -*
       balance_callback cl f (this ,, _field "C::balance")
         (∃ v' : Z, this |-> account_balanceR v' ** K)
     \post K).

  cpp.spec (account_call outer_lambda) as outer_call_spec from source with
    (\exact Reduce (call_spec_body outer_lambda)).
  cpp.spec (account_call inner_lambda) as inner_call_spec from source with
    (\exact Reduce (call_spec_body inner_lambda)).

  Local Lemma account_call_refines cl this args post :
    call_spec_body cl this args post |--
      account_call_internal_body cl this args post.
  Proof.
    rewrite /call_spec_body /account_call_internal_body.
    cbn.
    iIntros "H".
    iDestruct "H" as (f th gpool N q K)
      "(%Hargs & #Hf & #Hth & (HR & Hnames) & Hcallback & Hpost)".
    iEval (rewrite accountR.unlock _at_exists) in "HR".
    iDestruct "HR" as (g) "HR".
    iEval (rewrite !_at_sep !_at_pureR) in "HR".
    iDestruct "HR" as "(HR & Htoken & %Hg)".
    iAssert (std_recursive_mutex.acquireable (TT := balance_args) g q th
      std_recursive_mutex.NotHeld (fun n : Z => this |-> account_balanceR n))%I
      with "[Htoken Hnames]" as "Hacquireable".
    { rewrite -std_recursive_mutex.register_thread.
      destruct Hg as [Hgpool HN]. rewrite Hgpool HN. iFrame "#∗". }
    iExists f, g, q,
      (std_recursive_mutex.acquireable (TT := balance_args) g q th
         std_recursive_mutex.NotHeld (fun n : Z => this |-> account_balanceR n) ** K)%I.
    iFrame "Hf HR". iSplit; first done.
    iSplitR "Hpost".
    - rewrite /std_recursive_mutex.do_lock /=.
      iExists balance_args, (fun n : Z => this |-> account_balanceR n)%I,
        q, th, std_recursive_mutex.NotHeld.
      iSplit; first done. iFrame "Hacquireable".
      iIntros "Hlocked".
      iDestruct "Hlocked" as (s) "[%Hac Hlocked]".
      rewrite std_recursive_mutex.acquire.unlock in Hac.
      destruct Hac as [[v []] ->].
      iEval (rewrite /std_recursive_mutex.acquireable /=) in "Hlocked".
      iDestruct "Hlocked" as "(_ & Hheld & Hbalance)".
      iMod "Hheld". iMod "Hbalance". iModIntro.
      rewrite /balance_callback. iIntros (Q) "HQ".
      iSpecialize ("Hcallback" $! v with "Hbalance").
      iApply ("Hcallback" with "[-]").
      iIntros "Hresult".
      iDestruct "Hresult" as (v') "[Hbalance HK]".
      iApply "HQ".
      iExists balance_args, (fun n : Z => this |-> account_balanceR n)%I,
        q, th, 0%nat, (balance_arg v').
      iSplit; first done. iSplitL "Hheld Hbalance".
      { rewrite /std_recursive_mutex.acquireable /=. iFrame "#∗". }
      iIntros "Hunlocked".
      iEval (rewrite std_recursive_mutex.release.unlock) in "Hunlocked".
      iFrame.
    - iIntros "(HR & Hacquireable & HK)".
      iApply "Hpost". iFrame "HK".
      iEval (rewrite -std_recursive_mutex.register_thread) in "Hacquireable".
      iDestruct "Hacquireable" as "(_ & Htoken & Hnames)".
      destruct Hg as [Hgpool HN].
      iEval (rewrite Hgpool HN) in "Hnames". iFrame "Hnames".
      rewrite accountR.unlock _at_exists. iExists g.
      rewrite !_at_sep !_at_pureR. iFrame. done.
  Qed.

  Local Lemma outer_call_refines : outer_call_internal_spec |-- outer_call_spec.
  Proof. apply specify_mono. intros this args post. apply account_call_refines. Qed.

  Local Lemma inner_call_refines : inner_call_internal_spec |-- inner_call_spec.
  Proof. apply specify_mono. intros this args post. apply account_call_refines. Qed.

  Lemma outer_call_ok : verify?[source] outer_call_spec.
  Proof. work. wapply outer_call_refines. wapply outer_call_internal_ok. work. Qed.

  Lemma inner_call_ok : verify?[source] inner_call_spec.
  Proof. work. wapply inner_call_refines. wapply inner_call_internal_ok. work. Qed.

  cpp.spec "C::transfer(C&, unsigned long)" as C_transfer_spec from source with (
    \this from
    \arg{to} "to" (Vptr to)
    \arg{i} "i" (Vint i)
    \persist{th} current_thread th
    \prepost{gpool qfrom qto}
      from |-> accountR gpool from_namespace qfrom **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑from_namespace)) **
      to |-> accountR gpool to_namespace qto **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑to_namespace))
    \post emp
  ).

  Lemma C_transfer_ok : verify[source] C_transfer_spec.
  Proof.
    verify_spec; go.
    rewrite accountR.unlock. go.
    lazymatch goal with
    | |- context[transfer_lock_guard.R (this ,, _) ?gfrom _ _] =>
        rename gfrom into source_g
    end.
    iDestruct select (MutexSets.my_mutexes _ th
      (coPset.CoPset (↑from_namespace))) as "Hfrom_names".
    iEval (rewrite -b) in "Hfrom_names".
    iDestruct (bi.equiv_entails_1_1 _ _
      (std_recursive_mutex.register_thread source_g qfrom th (TT := balance_args)
        (fun n : Z => this |-> account_balanceR n)%I)
      with "[$]") as "?"; first go.
    iDestruct select (MutexSets.my_mutexes _ th
      (coPset.CoPset (↑to_namespace))) as "Hto_names".
    iEval (rewrite -a -b0) in "Hto_names".
    iDestruct (bi.equiv_entails_1_1 _ _
      (std_recursive_mutex.register_thread g qto th (TT := balance_args)
        (fun n : Z => to |-> account_balanceR n)%I)
      with "[$]") as "?"; first go.
    go.
    rewrite std_recursive_mutex.acquire.unlock in H1, H2.
    destruct H1 as [[from_balance []] Hfrom]. inversion Hfrom; subst.
    destruct H2 as [[to_balance []] Hto]. inversion Hto; subst.
    go.
    (* Return the updated destination balance when lg_to is destroyed. *)
    iExists (cQp.scale (1 / 2) qto),
      (std_recursive_mutex.acquireable (TT := balance_args) g qto th
        std_recursive_mutex.NotHeld (fun n : Z => to |-> account_balanceR n))%I.
    rewrite std_recursive_mutex.release.unlock /=. go.
    iSplitL ""; first by iIntros "$".
    go.
    (* Return the updated source balance when lg_from is destroyed. *)
    iExists (cQp.scale (1 / 2) qfrom),
      (std_recursive_mutex.acquireable (TT := balance_args) source_g qfrom th
        std_recursive_mutex.NotHeld (fun n : Z => this |-> account_balanceR n))%I.
    rewrite std_recursive_mutex.release.unlock /=. go.
    iSplitL ""; first by iIntros "$".
    go.
    rewrite accountR.unlock /std_recursive_mutex.acquireable. go with br_erefl.
    rewrite a b b0. go.
  Qed.

  (** Link the C implementation and both lock-guard operations. *)
  Lemma C_transfer_link :
    denoteModule source 
    ** std_recursive_mutex.std_lock_spec_alt 
    ** std_recursive_mutex.std_unlock_spec_alt
    |-- C_transfer_spec.
  Proof.
    work.
    wapply C_transfer_ok.
    wapply transfer_lock_guard.ctor_ok.
    wapply transfer_lock_guard.dtor_ok.
    work.
  Qed.

  #[local] Instance balanceR_tele_timeless (this : ptr) args :
    Timeless (tele_app (TT := balance_args) (fun n : Z => this |-> account_balanceR n) args).
  Proof. destruct args as [n []]. apply _. Qed.

  Section construction.
    (** FIXME this should be provable *)
    Context `{balance_objective : !forall (this : ptr) args,
      Objective (tele_app (TT := balance_args) (fun n : Z => this |-> account_balanceR n) args)}.

    cpp.spec "C::C(unsigned long)" as ctor_spec from source with (
      \this this
      \arg{initial_balance} "initial_balance" (Vint initial_balance)
      \persist{th} current_thread th
      \pre{gpool N} emp
      \post this |-> accountR gpool N 1$m
    ).

    Lemma ctor_ok : verify[source] ctor_spec.
    Proof using Type balance_objective.
      verify_spec; go.
      iExists gpool, N, balance_args, (fun n : Z => this |-> account_balanceR n)%I,
        (balance_arg initial_balance); go.
      rewrite -bi.later_intro.
      go.
      rewrite accountR.unlock. go with br_erefl.
    Qed.

  End construction.

  cpp.spec "C::~C()" as dtor_spec from source with (
    \this this
    \pre{gpool N} this |-> accountR gpool N 1$m
    \post emp
  ).

  Lemma dtor_ok : std_recursive_mutex.std_dtor_spec |-- verify[source] dtor_spec.
  Proof.
    verify_shift; go. rewrite accountR.unlock. go with br_erefl.
    match goal with
    | |- context[wp_destroy_named _ _ _ ?K] =>
        remember K as continuation eqn:Hcontinuation
    end.
    iModIntro. go. rewrite Hcontinuation.
    iDestruct select (bi_later (bi_exist _))
      as "Hbalance".
    iApply fupd_wp_destroy_val.
    iMod "Hbalance" as ([n []]) "Hbalance".
    iModIntro. go $usenamed=true.
  Qed.

End class_C.

Section clients.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!std_recursive_mutex.G Σ}.

  #[local] Instance accountR_learn :
    Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) accountR).
  Proof. solve_learnable. Qed.

  cpp.spec (lambda_call outer_lambda) from source inline.
  cpp.spec (lambda_call inner_lambda) from source inline.
  cpp.spec (Nscoped outer_lambda Ndtor) from source inline.
  cpp.spec (Nscoped inner_lambda Ndtor) from source inline.

  (* transfer balance with sequential ownership of the balances *)
  cpp.spec "transfer_seq(unsigned long&, unsigned long&, unsigned long)"
      as transfer_seq_spec from source with (
    \arg{b1} "b1" (Vptr b1)
    \arg{b2} "b2" (Vptr b2)
    \arg{i} "i" (Vint i)
    \pre{v1 v2} b1 |-> ulongR 1$m v1 ** b2 |-> ulongR 1$m v2
    \post b1 |-> ulongR 1$m (trim 64 (v1 - i)) **
      b2 |-> ulongR 1$m (trim 64 (v2 + i))).

  Lemma transfer_seq_ok : verify[source] transfer_seq_spec.
  Proof. verify_spec; go. Qed.

  (** Transfer balances using account ownership and per-thread namespace resources. *)
  cpp.spec "transfer(C&, C&, unsigned long)" as transfer_general_spec from source with (
    \arg{from} "from" (Vptr from)
    \arg{to} "to" (Vptr to)
    \arg{i} "i" (Vint i)
    \persist{th} current_thread th
    \prepost{gpool Nfrom Nto qfrom qto}
      from |-> accountR gpool Nfrom qfrom **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑Nfrom)) **
      to |-> accountR gpool Nto qto **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑Nto))
    \post emp).

  Local Lemma call_with_continuation (A : mpred -> mpred) R Q :
    A (R -* Q)%I |-- ∃ K, A K ** (R ** K -* Q).
  Proof.
    iIntros "HA". iExists (R -* Q)%I. iFrame "HA".
    iIntros "[HR HK]". iApply "HK". iFrame.
  Qed.

  Lemma transfer_general_ok : inner_call_spec ** transfer_seq_spec |-- verify[source] transfer_general_spec.
  Proof.
    verify_shift; go.
    iExists qfrom. go.
    iApply call_with_continuation.
    iIntros (v1) "Hfrom_balance".
    (* The outer acquisition exposes from's balance; to retains its account and namespace. *)
    wname [accountR] "Hto".
    iAssert (from |-> account_balanceR v1 ** to |-> accountR gpool Nto qto **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑Nto)))%I
      with "[$]" as "Hafter_from".
    iDestruct "Hafter_from" as "[? ?]".
    rewrite /balance_callback. iIntros (Qfrom) "HKfrom". go.
    iExists qto. go.
    iApply call_with_continuation.
    iIntros (v2) "Hto_balance".
    (* The inner acquisition exposes both balances. *)
    wname [account_balanceR] "Hfrom_balance".
    iAssert (from |-> account_balanceR v1 ** to |-> account_balanceR v2)%I
      with "[$Hfrom_balance $Hto_balance]" as "Hbefore_transfer".
    iDestruct "Hbefore_transfer" as "[? ?]".
    rewrite /balance_callback. iIntros (Qto) "HKto". go.
    (* After transfer_seq: unsigned subtraction/addition. *)
    iAssert (from ,, _field "C::balance" |-> ulongR 1$m (trim 64 (v1 - i)) **
      to ,, _field "C::balance" |-> ulongR 1$m (trim 64 (v2 + i)))%I
      with "[$]" as "Hafter_transfer".
    iDestruct "Hafter_transfer" as "[? ?]".
    iApply "HKto". go.
    (* Returning from to.call restores its account and namespace resource. *)
    iAssert (from ,, _field "C::balance" |-> ulongR 1$m (trim 64 (v1 - i)) **
      to |-> accountR gpool Nto qto **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑Nto)))%I
      with "[$]" as "Hafter_to".
    iDestruct "Hafter_to" as "(Hfrom_balance & Hto & Hto_names)".
    iApply "HKfrom". iExists (trim 64 (v1 - i)).
    iSplitL "Hfrom_balance".
    { iDestruct "Hfrom_balance" as "?". go. }
    iIntros "(Hfrom & Hfrom_names)".
    (* Returning from from.call restores both accounts and namespace resources. *)
    iAssert (from |-> accountR gpool Nfrom qfrom **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑Nfrom)) **
      to |-> accountR gpool Nto qto **
      MutexSets.my_mutexes gpool th (coPset.CoPset (↑Nto)))%I
      with "[$Hfrom $Hfrom_names $Hto $Hto_names]" as "Hafter_from".
    iDestruct "Hafter_from" as "[? ?]". go.
    wname [bi_wand] "Hpost".
    iSpecialize ("Hpost" with "[$]").
    iModIntro. iNext. iApply "Hpost". go.
  Qed.

  Lemma transfer_general_link :
    denoteModule source ** outer_call_spec ** inner_call_spec |-- transfer_general_spec.
  Proof.
    work. wapply transfer_general_ok. wapply transfer_seq_ok. work.
  Qed.

  (** Choose both mutex namespaces for the callback-based transfer. *)
  Definition transfer_body : WpSpec mpred val val :=
    (
  \arg{from} "from" (Vptr from)
  \arg{to} "to" (Vptr to)
  \arg{i} "i" (Vint i)
  \persist{th} current_thread th
  \prepost{gpool qfrom qto}
    from |-> accountR gpool from_namespace qfrom **
    MutexSets.my_mutexes gpool th (coPset.CoPset (↑from_namespace)) **
    to |-> accountR gpool to_namespace qto **
    MutexSets.my_mutexes gpool th (coPset.CoPset (↑to_namespace))
  \post emp
    ).

  cpp.spec "transfer(C&, C&, unsigned long)" as transfer_spec from source with
    (\exact Reduce transfer_body).

  Lemma transfer_specialize : transfer_general_spec |-- transfer_spec.
  Proof.
    apply specify_mono. intros args post. cbn.
    work.
    iExists qfrom, qto. work.
  Qed.

  Lemma transfer_ok : inner_call_spec ** transfer_seq_spec |-- verify[source] transfer_spec.
  Proof. work. wapply transfer_specialize. wapply transfer_general_ok. work. Qed.

  Lemma transfer_link :
    denoteModule source ** outer_call_spec ** inner_call_spec |-- transfer_spec.
  Proof. work. wapply transfer_specialize. wapply transfer_general_link. work. Qed.

  cpp.spec "main()" as main_spec from source with (
    \persist{th} current_thread th
    \post[Vint 0] emp
  ).

  Lemma main_ok : verify[source] main_spec.
  Proof.
    verify_spec.
    let rec allocate_pool :=
      first [iMod MutexSets.alloc_mutex_set_map as (gpool) "Hmap"
            | progress go1; allocate_pool] in
    allocate_pool.
    iMod (MutexSets.mutex_sets_alloc_thread gpool ∅ th ltac:(set_solver)
      with "Hmap") as "[Hmap Hnames]".
    iEval (rewrite left_id_L) in "Hmap".
    go.
    iExists gpool, from_namespace; go.
    iExists gpool, to_namespace; go.
    have Hdisjoint := transfer_namespaces_disjoint.
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name gpool th ⊤
      (↑from_namespace) ltac:(set_solver)
      with "Hnames") as "[Hnames Hfrom]".
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name gpool th
      (⊤ ∖ ↑from_namespace)
      (↑to_namespace) ltac:(set_solver)
      with "Hnames") as "[Hnames Hto]".
    iDestruct "Hfrom" as "?". iDestruct "Hto" as "?".
    go. iExists (1$m)%cQp, (1$m)%cQp. go.
    iDestruct (MutexSets.my_mutexes_join_mutex_name gpool th
      (⊤ ∖ ↑from_namespace)
      (↑to_namespace) ltac:(set_solver)
      with "[$]") as "Hnames".
    iDestruct (MutexSets.my_mutexes_join_mutex_name gpool th ⊤
      (↑from_namespace) ltac:(set_solver)
      with "[$]") as "Hnames".
    iDestruct (MutexSets.mutex_sets_free_thread gpool {[th]} th
      ltac:(set_solver) with "[$]") as "Hmap".
    iEval (rewrite difference_diag_L) in "Hmap".
    iDestruct "Hmap" as "?".
    iDestruct select (MutexSets.mutex_set_map _ _) as "Hmap".
    iApply (affine with "Hmap"). apply mpred_BiAffine.
  Qed.

  (* FIXME do we need this? *)
  Lemma main_link `{balance_objective : !forall (this : ptr) args,
      Objective (tele_app (TT := balance_args) (fun n : Z => this |-> account_balanceR n) args)} :
    denoteModule source ** std_recursive_mutex.std_ctor_spec ** std_recursive_mutex.std_dtor_spec **
      std_recursive_mutex.std_lock_spec_alt ** std_recursive_mutex.std_unlock_spec_alt |-- main_spec.
  Proof.
    work.
    wapply main_ok.
    wapply ctor_ok.
    wapply dtor_ok.
    wapply transfer_link.
    wapply outer_call_ok.
    wapply inner_call_ok.
    wapply transfer_lock_guard.ctor_ok.
    wapply transfer_lock_guard.dtor_ok.
    work.
  Qed.
End clients.
