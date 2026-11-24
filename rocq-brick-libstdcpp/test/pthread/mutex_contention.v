(* Copyright (c) 2026 SkyLabs AI, Inc. SPDX-License-Identifier: BSD-3-Clause *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_cpp.

Module PM := pthread.mutex.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.
  Context `{!mutex_set_G Σ, !PM.G Σ}.
  Context `{Hmodule : !source ⊧ σ}.

  Section held.
    Definition held_trylock := RegisterSpec PM.trylock_held_spec.
    #[local] Existing Instance held_trylock.

    (* The calling thread need not be the thread named by the held token. *)
    cpp.spec "try_when_held(pthread_mutex_t*)" as try_when_held_spec with (
      \arg{m} "mutex" (Vptr m)
      \prepost{g q P} m |-> PM.R g q P
      \prepost{owner qt} PM.locked m g owner qt
      \post[Vint PM.EBUSY] emp).

    Lemma try_when_held_ok : verify[source] try_when_held_spec.
    Proof. verify_spec; go.  iExists owner, qt. go. Qed.
  End held.

  Section free.
    Definition free_trylock := RegisterSpec PM.trylock_uncontended_spec.
    #[local] Existing Instance free_trylock.

    cpp.spec "try_when_free(pthread_mutex_t*)" as try_when_free_spec with (
      \arg{m} "mutex" (Vptr m)
      \prepost{g P} m |-> PM.R g 1$m P
      \persist{th} current_thread th
      \pre PM.not_locked m g th 1$m
      \post[Vint 0] PM.locked m g th 1$m ** P).

    Lemma try_when_free_ok : verify[source] try_when_free_spec.
    Proof. verify_spec; go. Qed.
  End free.
End with_cpp.
