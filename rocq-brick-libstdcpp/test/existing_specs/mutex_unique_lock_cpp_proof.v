
Require Import mutex_unique_lock_cpp.

Require Import skylabs.brick.libstdcpp.mutex.spec.unique_lock.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.lib.tactics.
Require Import skylabs.auto.cpp.prelude.proof.

Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

Require Import skylabs.auto.cpp.proof.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : mutex_unique_lock_cpp.source ⊧ σ}.

Goal SpecFor mutex_unique_lock_cpp.source "std::unique_lock<std::mutex>::unique_lock()".
Proof. eapply unique_lock.default_ctor_spec_spec_instance.

Restart.
constructor.
exact emp.
Qed.

  Context (STD_THREADS : HasStdThreads Σ).
  #[local] Existing Instance STD_THREADS.

  Lemma default_ctor_registration_available :
    SpecFor mutex_unique_lock_cpp.source
      "std::unique_lock<std::mutex>::unique_lock()".
  Proof using STD_THREADS. typeclasses eauto. Qed.

  cpp.spec "default_and_observer_oracle()" as default_and_observer_oracle_spec
    from mutex_unique_lock_cpp.source with (
      \post[Vbool true] emp).

  Lemma default_and_observer_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "default_and_observer_oracle()".
  Proof using STD_THREADS.
    verify_spec.

    go $usenamed=true.

  Qed.

  cpp.spec "locking_constructor_oracle()" as locking_constructor_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "deferred_transition_oracle()" as deferred_transition_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "move_construction_oracle()" as move_construction_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "move_assignment_primary_oracle()" as move_assignment_primary_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "move_assignment_alternative_oracle()" as move_assignment_alternative_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "destructor_primary_oracle()" as destructor_primary_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "destructor_alternative_oracle()" as destructor_alternative_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).
  cpp.spec "guarded_composition_oracle()" as guarded_composition_oracle_spec
    from mutex_unique_lock_cpp.source with (\post[Vbool true] emp).

  Lemma locking_constructor_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "locking_constructor_oracle()".
  Proof using STD_THREADS.
    verify_spec.

    go $usenamed=true.

    iExists emp%I.

    iSplit; first done.

    iIntros "(%g & Hmutex & Htoken)".

    go $usenamed=true.

  Qed.

  Require Import skylabs.brick.libstdcpp.mutex.spec.defer_lock_t.

  Lemma deferred_transition_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "deferred_transition_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%g & Hmutex & Htoken)".
    go $usenamed=true.

    iExists (1$m)%cQp.

    go $usenamed=true.

  Abort.

  cpp.spec "deferred_transition_oracle()" as deferred_transition_oracle_tagged_spec
    from mutex_unique_lock_cpp.source with (
      \pre{q : cQp.t}
        _global "std::defer_lock" |-> defer_lock_t.R q
      \post[Vbool true]
        _global "std::defer_lock" |-> defer_lock_t.R q).

  Lemma deferred_transition_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "deferred_transition_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%g & Hmutex & Htoken)".
    go $usenamed=true.

  Qed.

  cpp.spec "move_construction_oracle()" as move_construction_oracle_tagged_spec
    from mutex_unique_lock_cpp.source with (
      \pre{q : cQp.t} _global "std::defer_lock" |-> defer_lock_t.R q
      \post[Vbool true] _global "std::defer_lock" |-> defer_lock_t.R q).
  cpp.spec "move_assignment_alternative_oracle()" as move_assignment_alternative_oracle_tagged_spec
    from mutex_unique_lock_cpp.source with (
      \pre{q : cQp.t} _global "std::defer_lock" |-> defer_lock_t.R q
      \post[Vbool true] _global "std::defer_lock" |-> defer_lock_t.R q).
  cpp.spec "destructor_primary_oracle()" as destructor_primary_oracle_tagged_spec
    from mutex_unique_lock_cpp.source with (
      \pre{q : cQp.t} _global "std::defer_lock" |-> defer_lock_t.R q
      \post[Vbool true] _global "std::defer_lock" |-> defer_lock_t.R q).
  cpp.spec "destructor_alternative_oracle()" as destructor_alternative_oracle_tagged_spec
    from mutex_unique_lock_cpp.source with (
      \pre{q : cQp.t} _global "std::defer_lock" |-> defer_lock_t.R q
      \post[Vbool true] _global "std::defer_lock" |-> defer_lock_t.R q).
  cpp.spec "guarded_composition_oracle()" as guarded_composition_oracle_tagged_spec
    from mutex_unique_lock_cpp.source with (
      \pre{q : cQp.t} _global "std::defer_lock" |-> defer_lock_t.R q
      \post[Vbool true] _global "std::defer_lock" |-> defer_lock_t.R q).

  Lemma move_construction_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "move_construction_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

  Abort.

  cpp.spec
    "std::move<std::unique_lock<std::mutex>&>(std::unique_lock<std::mutex>&)"
    as std_move_unique_lock_spec from mutex_unique_lock_cpp.source with (
      \arg{p} "" (Vref p)
      \post[Vptr p] emp).

  Lemma std_move_unique_lock_ok :
    verify[mutex_unique_lock_cpp.source]
      "std::move<std::unique_lock<std::mutex>&>(std::unique_lock<std::mutex>&)".
  Proof.
    verify_spec.
    go $usenamed=true.
  Qed.
  #[local] Instance inline_std_move_unique_lock :
    ShouldInlineFunction
      "std::move<std::unique_lock<std::mutex>&>(std::unique_lock<std::mutex>&)" := {}.

  Lemma move_construction_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "move_construction_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%g & Hmutex & Htoken)".
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%g2 & Hmutex2 & Htoken2)".
    go $usenamed=true.

  Qed.

  Lemma move_assignment_primary_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "move_assignment_primary_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%gold & Hmutex_old & Htoken_old)".
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%gnew & Hmutex_new & Htoken_new)".
    go $usenamed=true.

    iExists (mutex.token gold (1 / 2) **
      old_mutex_addr |-> mutex.R gold (1 / 2)$m emp)%I.
    go $usenamed=true.

    iSplitR.

    - iIntros "Htoken_returned Hmutex_returned". iFrame.
    - iIntros "(Hdestination & Hsource & Htoken_old_returned & Hmutex_old_returned)".
      go $usenamed=true.

  Qed.

  Section select_move_assign_alt.
    #[local] Remove Hints unique_lock.move_assign_spec_spec_instance : typeclass_instances.

    Lemma move_assignment_alternative_oracle_ok :
      verify[mutex_unique_lock_cpp.source] "move_assignment_alternative_oracle()".
    Proof using STD_THREADS.
      verify_spec.
      go $usenamed=true.

      iExists emp%I.
      iSplit; first done.
      iIntros "(%g & Hmutex & Htoken)".
      go $usenamed=true.

    Qed.
  End select_move_assign_alt.

  Lemma destructor_alternative_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "destructor_alternative_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%g & Hmutex & Htoken)".
    go $usenamed=true.

  Qed.

  Section select_dtor_primary.
    #[local] Remove Hints unique_lock.dtor_spec_alt_spec_instance : typeclass_instances.

    Lemma destructor_primary_oracle_ok :
      verify[mutex_unique_lock_cpp.source] "destructor_primary_oracle()".
    Proof using STD_THREADS.
      verify_spec.
      go $usenamed=true.

      iExists emp%I.
      iSplit; first done.
      iIntros "(%g & Hmutex & Htoken)".
      go $usenamed=true.

      iExists (mutex.token g (1 / 2) **
        mutex_addr |-> mutex.R g (1 / 2)$m emp)%I.
      iSplitR.
      - iIntros "Htoken_returned Hmutex_returned". iFrame.
      - iIntros "(Htoken_returned & Hmutex_returned)".
        go $usenamed=true.

    Qed.
  End select_dtor_primary.

  Lemma guarded_composition_oracle_ok :
    verify[mutex_unique_lock_cpp.source] "guarded_composition_oracle()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

    iExists emp%I.
    iSplit; first done.
    iIntros "(%g & Hmutex & Htoken)".
    go $usenamed=true.

  Qed.

  cpp.spec "main()" as main_spec from mutex_unique_lock_cpp.source with (
    \prepost{q : cQp.t}
      _global "std::defer_lock" |-> defer_lock_t.R q
    \post[Vint 0] emp).

  Lemma main_ok : verify[mutex_unique_lock_cpp.source] "main()".
  Proof using STD_THREADS.
    verify_spec.
    go $usenamed=true.

  Qed.

  Lemma empty_or_moved_from_cannot_match_lock_precondition
      (mm : unique_lock.M mutex.T) :
    None = Some mm -> False.
  Proof. discriminate. Qed.

  Lemma owning_state_cannot_match_lock_precondition
      (mm : unique_lock.M mutex.T) :
    mm.(unique_lock.is_held) = true ->
    ~~ mm.(unique_lock.is_held) = true -> False.
  Proof. destruct mm as [held mp q m]; simpl. destruct held; simpl; congruence. Qed.

  Lemma released_state_cannot_match_unlock_precondition
      (mm : unique_lock.M mutex.T) :
    mm.(unique_lock.is_held) = false ->
    mm.(unique_lock.is_held) = true -> False.
  Proof. congruence. Qed.

  Lemma mutex_locking_twice_unreachable
      (g : gname) (thr : thread_idT) (q : Qp) :
    mutex.locked g thr q ** mutex.locked g thr q |-- False.
  Proof. go $usenamed=true.

    wname [mutex.locked g thr q] "Hlocked1".
    wname [mutex.locked g thr q] "Hlocked2".

    iPoseProof (token_excl (ExclusiveToken:=
      mutex.locked_exclusive STD_THREADS σ g thr q)
      with "Hlocked1 Hlocked2") as "Hfalse".
    iExact "Hfalse".
  Qed.

  Lemma move_source_destination_representations_exclusive :
    let lockR := unique_lock.R "std::mutex"
      (fun q gammaP => mutex.R gammaP.1 q gammaP.2) in
    Observe2 False (lockR (1$m)%cQp None) (lockR (1$m)%cQp None).
  Proof. cbn.
    exact (@cfrac_0_exclusive Rep
      (fun q : cQp.t => unique_lock.R "std::mutex"
        (fun q gammaP => mutex.R gammaP.1 q gammaP.2) q None)
      _ _ (1$m)%cQp _ (1$m)%cQp).
  Qed.

  Lemma associated_lock_carries_mutex_lifetime
      (q : cQp.t) (mm : unique_lock.M mutex.T) :
    unique_lock.R "std::mutex"
      (fun q gammaP => mutex.R gammaP.1 q gammaP.2) q (Some mm)
    |-- pureR (mm.(unique_lock.mutex_ptr) |->
      mutex.R mm.(unique_lock.mutex_m).1
        (cQp.scale mm.(unique_lock.mutex_q) q)
        mm.(unique_lock.mutex_m).2).
  Proof. rewrite unique_lock.R.unlock. go $usenamed=true. Qed.

  Lemma held_ensure_unlock_requires_release
      (mp : ptr) (q : Qp) (gammaP : mutex.T) (K : mpred) :
    unique_lock.ensure_unlock "std::mutex"
      (Some {| unique_lock.is_held := true;
               unique_lock.mutex_ptr := mp;
               unique_lock.mutex_q := q;
               unique_lock.mutex_m := gammaP |}) K
    = requirements.do_unlock "std::mutex" mp gammaP
        (mp |-> mutex.R gammaP.1 (q$m)%cQp gammaP.2 -* K).
  Proof. reflexivity. Qed.

  Lemma held_alternative_branch_requires_release
      (mp : ptr) (q : Qp) (gammaP : mutex.T) (K : mpred) :
    (match Some {| unique_lock.is_held := true;
                   unique_lock.mutex_ptr := mp;
                   unique_lock.mutex_q := q;
                   unique_lock.mutex_m := gammaP |} with
     | Some mm =>
         if mm.(unique_lock.is_held)
         then requirements.do_unlock "std::mutex"
                mm.(unique_lock.mutex_ptr) mm.(unique_lock.mutex_m) K
         else K
     | None => K
     end)
    = requirements.do_unlock "std::mutex" mp gammaP K.
  Proof. reflexivity. Qed.

End with_cpp.
