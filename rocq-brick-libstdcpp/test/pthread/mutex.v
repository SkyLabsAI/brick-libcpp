(* Copyright (c) 2026 SkyLabs AI, Inc. SPDX-License-Identifier: BSD-3-Clause *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.test.pthread.mutex_cpp.

Import linearity.
Module PM := pthread.mutex.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.
  Context `{!mutex_set_G Σ, !PM.G Σ}.
  Context `{Hmodule : !source ⊧ σ}.

  (* The protected cell is available only between successful acquisition and
     release. Ignoring the lock/unlock results is sound under these premises. *)
  cpp.spec "read_locked(pthread_mutex_t*, int*)" as read_locked_spec with (
    \arg{m} "mutex" (Vptr m)
    \arg{p} "value" (Vptr p)
    \prepost{g q x} m |-> PM.R g q (p |-> intR 1$m x)
    \persist{th} current_thread th
    \prepost{qt} PM.not_locked m g th qt
    \post[Vint x] emp).

  cpp.spec "try_read(pthread_mutex_t*, int*, int*)" as try_read_spec with (
    \arg{m} "mutex" (Vptr m)
    \arg{p} "value" (Vptr p)
    \arg{out} "result" (Vptr out)
    \prepost{g q x} m |-> PM.R g q (p |-> intR 1$m x)
    \persist{th} current_thread th
    \prepost{qt} PM.not_locked m g th qt
    \pre{old} out |-> intR 1$m old
    \post{success : bool}[Vbool success]
      out |-> intR 1$m (if success then x else old)).

  cpp.spec "try_while_owned(pthread_mutex_t*)" as try_while_owned_spec with (
    \arg{m} "mutex" (Vptr m)
    \prepost{g q P} m |-> PM.R g q P
    \persist{th} current_thread th
    \prepost{qt} PM.locked m g th qt
    \post[Vint PM.EBUSY] emp).

  cpp.spec "relock_while_owned(pthread_mutex_t*)" as relock_while_owned_spec with (
    \arg{m} "mutex" (Vptr m)
    \pre{g q P} m |-> PM.R g q P
    \persist{th} current_thread th
    \pre{qt} PM.locked m g th qt
    \post False).

  cpp.spec "initialize_default(pthread_mutex_t*)" as initialize_default_spec with (
    \arg{m} "mutex" (Vptr m)
    \pre m |-> anyR "pthread_mutex_t" 1$m
    \pre{N P} ▷P
    \require N <> nroot
    \require WeaklyObjective P
    \post |={⊤}=> ∃ g, [|PM.mutex_inv_namespace g = N|] **
      m |-> PM.R g 1$m P ** PM.token g 1$m).

  cpp.spec "destroy_default(pthread_mutex_t*)" as destroy_default_spec with (
    \arg{m} "mutex" (Vptr m)
    \pre{g P} m |-> PM.R g 1$m P ** PM.token g 1$m
    \post m |-> anyR "pthread_mutex_t" 1$m ** P).

  cpp.spec "self_equal()" as self_equal_spec with (
    \persist{th} current_thread th
    \post[Vbool true] emp).

  Lemma read_locked_ok : verify[source] read_locked_spec.
  Proof. verify_spec; go. Qed.

  Lemma try_read_ok : verify[source] try_read_spec.
  Proof. verify_spec; go. destruct _x_; go. Qed.

  Section owner_rules.
    Definition owner_trylock := RegisterSpec PM.trylock_owned_spec.
    #[local] Existing Instance owner_trylock.
    Definition owner_lock := RegisterSpec PM.lock_owned_spec.
    #[local] Existing Instance owner_lock.

    Lemma try_while_owned_ok : verify[source] try_while_owned_spec.
    Proof. verify_spec; go. Qed.

    Lemma relock_while_owned_ok : verify[source] relock_while_owned_spec.
    Proof. verify_spec; go. Qed.
  End owner_rules.

  Lemma initialize_default_ok : verify[source] initialize_default_spec.
  Proof. verify_spec; go. iExists N, P. go. Qed.

  Lemma destroy_default_ok : verify[source] destroy_default_spec.
  Proof. verify_spec; go. Qed.

  Lemma self_equal_ok : verify[source] self_equal_spec.
  Proof. verify_spec; go. iPureIntro. rewrite bool_decide_true; done. Qed.

  Section linux_runtime.
    Definition nonzero_self := RegisterSpec pthread.self_nonzero_spec.
    #[local] Existing Instance nonzero_self.

    cpp.spec "self_is_zero()" as self_is_zero_spec with (
      \persist pthread.linux_thread_context
      \persist{th} current_thread th
      \post[Vbool false] emp).

    Lemma self_is_zero_ok : verify[source] self_is_zero_spec.
    Proof. verify_spec; go. iPureIntro. rewrite bool_decide_false; lia. Qed.
  End linux_runtime.
End with_cpp.
