(* Copyright (c) 2026 SkyLabs AI, Inc. SPDX-License-Identifier: BSD-3-Clause *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.cpp.zeroR.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_cpp.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex.

Import linearity.
#[local] Hint Opaque zeroR : sl_opacity typeclass_instances.
Module PM := pthread.mutex.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.
  Context `{!mutex_set_G Σ, !PM.G Σ}.
  Context `{Hmodule : !source ⊧ σ}.

  #[local] Instance protected_cell_weakly_objective (p : ptr) x :
      WeaklyObjective (p |-> intR 1$m x).
  Proof using Type HasStdThreads0. apply LocalWith_procTI_weakly_objective, _. Qed.

  cpp.spec "read_static_then_destroy(int*)" as static_client_spec with (
    \arg{p} "value" (Vptr p)
    \pre _global "static_mutex" |-> type_ptrR "pthread_mutex_t"
    \pre _global "static_mutex" |-> zeroR "pthread_mutex_t" 1$m
    \pre{x} p |-> intR 1$m x
    \persist{th} current_thread th
    \prepost MutexSets.my_mutexes th (coPset.CoPset ⊤)
    \post[Vint x] _global "static_mutex" |-> anyR "pthread_mutex_t" 1$m **
      p |-> intR 1$m x).

  cpp.spec "read_zero_then_destroy(int*)" as zero_client_spec with (
    \arg{p} "value" (Vptr p)
    \pre _global "zero_mutex" |-> type_ptrR "pthread_mutex_t"
    \pre _global "zero_mutex" |-> zeroR "pthread_mutex_t" 1$m
    \pre{x} p |-> intR 1$m x
    \persist{th} current_thread th
    \prepost MutexSets.my_mutexes th (coPset.CoPset ⊤)
    \post[Vint x] _global "zero_mutex" |-> anyR "pthread_mutex_t" 1$m **
      p |-> intR 1$m x).

  Lemma static_client_ok : verify[source] static_client_spec.
  Proof using Type Hmodule.
    verify_spec.
    iPoseProof (PM.setup_initializer (_global "static_mutex")
      (Namespace [1%positive]) (p |-> intR 1$m x)
      ltac:(discriminate) ltac:(apply _)) as "Hsetup".
    iEval (rewrite _at_type_ptrR) in "Hsetup".
    iDestruct select (p |-> intR 1$m x) as "Hvalue".
    iDestruct select (_global "static_mutex" |-> zeroR "pthread_mutex_t" 1$m) as "Hzero".
    iMod ("Hsetup" with "[Hvalue Hzero]") as (g) "(%HN & Hm & Htoken)".
    { iFrame "Hzero". iSplit; first iFrame "#". iNext. iFrame. }
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name th ⊤
      (↑PM.mutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    iAssert (PM.not_locked (_global "static_mutex") g th (1$m)%cQp)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /PM.not_locked. iFrame. }
    go $usenamed=true.
    iExists (1$m)%cQp, x. go $usenamed=true.
    iDestruct select (PM.not_locked _ _ _ _) as "Hnotlocked".
    iEval (rewrite /PM.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name th ⊤
      (↑PM.mutex_inv_namespace g) ltac:(set_solver)
      with "[$Hrest $Hname]") as "Hnames".
    go $usenamed=true.
  Qed.

  Lemma zero_client_ok : verify[source] zero_client_spec.
  Proof using Type Hmodule.
    verify_spec.
    iPoseProof (PM.setup_zero (_global "zero_mutex")
      (Namespace [2%positive]) (p |-> intR 1$m x)
      ltac:(discriminate) ltac:(apply _)) as "Hsetup".
    iEval (rewrite _at_type_ptrR) in "Hsetup".
    iDestruct select (p |-> intR 1$m x) as "Hvalue".
    iDestruct select (_global "zero_mutex" |-> zeroR "pthread_mutex_t" 1$m) as "Hzero".
    iMod ("Hsetup" with "[Hvalue Hzero]") as (g) "(%HN & Hm & Htoken)".
    { iFrame "Hzero". iSplit; first iFrame "#". iNext. iFrame. }
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name th ⊤
      (↑PM.mutex_inv_namespace g) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    iAssert (PM.not_locked (_global "zero_mutex") g th (1$m)%cQp)
      with "[Htoken Hname]" as "Hnotlocked".
    { rewrite /PM.not_locked. iFrame. }
    go $usenamed=true.
    iExists (1$m)%cQp, x. go $usenamed=true.
    iDestruct select (PM.not_locked _ _ _ _) as "Hnotlocked".
    iEval (rewrite /PM.not_locked) in "Hnotlocked".
    iDestruct "Hnotlocked" as "[Htoken Hname]".
    iDestruct (MutexSets.my_mutexes_join_mutex_name th ⊤
      (↑PM.mutex_inv_namespace g) ltac:(set_solver)
      with "[$Hrest $Hname]") as "Hnames".
    go $usenamed=true.
  Qed.
End with_cpp.
