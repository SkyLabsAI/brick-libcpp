(* Copyright (c) 2026 SkyLabs AI, Inc. SPDX-License-Identifier: BSD-3-Clause *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.owner_cpp.

Module PM := pthread.mutex.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.
  Context `{!mutex_set_G Σ, !PM.G Σ}.
  Context `{Hmodule : !source ⊧ σ}.

  cpp.spec "remember_owner(pthread_mutex_t*, unsigned long*)" as remember_spec with (
    \arg{m} "mutex" (Vptr m)
    \arg{owner} "owner" (Vptr owner)
    \prepost{g q} m |-> PM.R g q (owner |-> ulongR 1$m 0)
    \persist{th} current_thread th
    \pre{qt} PM.not_locked m g th qt
    \post (PM.locked m g th qt ** owner |-> ulongR 1$m (wrap.unwrapN th)) ∨
      PM.not_locked m g th qt).

  cpp.spec "remember_owner(pthread_mutex_t*, unsigned long*)" as remember_owned_spec with (
    \arg{m} "mutex" (Vptr m)
    \arg{owner} "owner" (Vptr owner)
    \prepost{g q P} m |-> PM.R g q P
    \persist{th} current_thread th
    \prepost{qt} PM.locked m g th qt
    \prepost{x} owner |-> ulongR 1$m x
    \post emp).

  cpp.spec "clear_owner_and_unlock(pthread_mutex_t*, unsigned long*)" as clear_spec with (
    \arg{m} "mutex" (Vptr m)
    \arg{owner} "owner" (Vptr owner)
    \prepost{g q} m |-> PM.R g q (owner |-> ulongR 1$m 0)
    \persist{th} current_thread th
    \pre{qt} PM.locked m g th qt
    \pre{x} owner |-> ulongR 1$m x
    \post PM.not_locked m g th qt).

  cpp.spec "owner_is_self(const unsigned long*)" as owner_is_self_spec with (
    \arg{owner} "owner" (Vptr owner)
    \persist{th} current_thread th
    \prepost{q} owner |-> ulongR q (wrap.unwrapN th)
    \post[Vbool true] emp).

  cpp.spec "resume_owned(pthread_mutex_t*, unsigned long*)" as resume_spec with (
    \arg{m} "mutex" (Vptr m)
    \arg{owner} "owner" (Vptr owner)
    \prepost{g q P} m |-> PM.R g q P
    \persist{th} current_thread th
    \prepost{qt} PM.locked m g th qt
    \prepost owner |-> ulongR 1$m (wrap.unwrapN th)
    \post[Vbool true] emp).

  Lemma remember_ok : verify[source] remember_spec.
  Proof. verify_spec; go. destruct _x_; go.  { iLeft. iFrame. } { iRight. iFrame. } Qed.

  Section owned.
    Definition owned_trylock := RegisterSpec PM.trylock_owned_spec.
    #[local] Existing Instance owned_trylock.

    Lemma remember_owned_ok : verify[source] remember_owned_spec.
    Proof. verify_spec; go. Qed.
  End owned.

  Lemma clear_ok : verify[source] clear_spec.
  Proof. verify_spec; go. Qed.

  Lemma owner_is_self_ok : verify[source] owner_is_self_spec.
  Proof. verify_spec; go. iPureIntro. rewrite bool_decide_true; done. Qed.

  Lemma resume_ok : verify[source] resume_spec.
  Proof. verify_spec; go. Qed.
End with_cpp.
