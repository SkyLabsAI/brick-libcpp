(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.mutex.requirements.

Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.pthread.hints.
Require Import skylabs.brick.libstdcpp.cassert.spec.

Require Import skylabs.brick.libstdcpp.test.pthread.test_cpp.

Require Import skylabs.auto.cpp.prelude.proof.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!test_cpp.source ⊧ σ}.

  cpp.spec "thread_fn(void*)" as thread_fn_spec with
      ( \arg{argp} "arg" (Vptr argp)
        \pre{x}  argp |-> intR 1$m x
        \post*   argp |-> intR 1$m (x + 1)
        \require valid<"int"> (x + 1)
        \post[Vptr nullptr] emp ).

  cpp.spec "cancelable_thread(void*)" as cancelable_thread_spec with
      ( \arg{argp} "arg" (Vptr argp)
        \pre{x}       argp |-> intR 1$m x
        \post*        argp |-> intR 1$m (x + 3)
        \require      valid<"int"> (x + 3)  (* TODO: validP / valid should be interchageable *)
        \post[Vptr nullptr] emp ).

    cpp.spec "multithreaded_broken()" as multithreaded_broken_spec with
      ( \post emp ).

    cpp.spec "multithreaded_ok()" as multithreaded_ok_spec with
      ( \post emp ).

End with_cpp.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{Hmodule : !test_cpp.source ⊧ σ}.
  Set Default Proof Using "Hmodule".

  #[local] Arguments tele_app _ _ & _.
  #[local] Hint Opaque tele_app : sl_opacity.

  #[global] Instance thread_fn_is_thread :
    ThreadFunction "thread_fn(void*)" thread_fn_spec
      [tele (_ : Z)]
      (fun p => tele_app (fun x => p |-> intR 1$m x ∗ [| valid<"int"> (x + 1) |]))%I
      (fun p => tele_app (fun x _tid => p |-> intR 1$m (x + 1)))%I.
  Proof. eapply specify_mono; work. Qed.

  #[global] Instance cancelable_thread_fn_is_thread :
    ThreadFunction "cancelable_thread(void* )" cancelable_thread_spec
      [tele (_ : Z)]
      (fun p => tele_app $ fun x => p |-> intR 1$m x ∗ [| valid<"int"> (x + 3) |] )%I
      (fun p => tele_app $ fun x _retp => p |-> intR 1$m (x + 3))%I.
  Proof. eapply specify_mono; work. Qed.

  Lemma thread_fn_ok : verify[source] thread_fn_spec.
  Proof.
    verify_spec. go.
  Qed.

  Lemma multithreaded_broken_ok : verify[source] multithreaded_broken_spec.
  Proof.
    verify_spec. go.
    wp_if.
    { go. }
    go.
    (* fails here because thread owns local variable [counter] *)
  Fail Qed.
  Abort.

  Lemma multithreaded_ok_ok : verify[source] multithreaded_ok_spec.
  Proof.
    verify_spec. go.
      (* fork thread 1 *)
    wp_if; go; [].
      (* fork thread 2 *)
    wp_if.
    { go. }
    go.
  Qed.

End with_cpp.
