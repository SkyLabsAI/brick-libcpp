(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * A thread joins a thread that another thread created (SkyLabsAI/brick-libcpp#259)

    [test()] creates W, then hands W's handle to S through S's argument, and S joins W.
    [pthread.handle_local_with] lets the handle move to S, since W's payload, [count]'s
    cell, is not specific to a thread. S is generic in the payload it joins for.

    Every join may fail (<<EDEADLK>>). W then still runs with [test()]'s local [count], so
    the joiner aborts. *)

Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.brick.libstdcpp.test.pthread.join_other_thread_cpp.
Require Import skylabs.auto.cpp.prelude.proof.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.
  #[local] Abbreviation taS := skylabs.auto.telescopes.taS.
  #[local] Abbreviation taO := skylabs.auto.telescopes.taO.

  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MOD : !join_other_thread_cpp.source ⊧ σ}.

  #[local] Arguments tele_app _ _ & _.
  #[local] Hint Opaque tele_app : sl_opacity.

  #[local] Instance pthread_R_local_with q th : LocalWithR procTI (pthread.R q th).
  Proof. rewrite pthread.R.unlock. apply _. Qed.

  (** W increments the [int] it is given. *)
  #[local] Abbreviation PreW :=
    (fun (p : ptr) (_ : tele_arg [tele]) => p |-> intR 1$m 0) (only parsing).
  #[local] Abbreviation PostW :=
    (fun (p : ptr) (_ : tele_arg [tele]) (_ : thread_idT) => p |-> intR 1$m 1) (only parsing).

  (** S takes the id of a thread and a handle for it, with any payload [P], and returns
      [P]. *)
  #[local] Abbreviation StopT :=
    [tele (_ : pthread.gname) (_ : thread_idT) (_ : mpred)]%ptele.
  #[local] Abbreviation PreS :=
    (fun (p : ptr) (a : tele_arg StopT) =>
       tele_app (t := StopT)
         (fun γ tid P => p |-> pthread.R 1$m tid ** pthread.handle γ tid P) a)
    (only parsing).
  #[local] Abbreviation PostS :=
    (fun (p : ptr) (a : tele_arg StopT) (_ : thread_idT) =>
       tele_app (t := StopT) (fun γ tid P => p |-> pthread.R 1$m tid ** P) a)
    (only parsing).

  cpp.spec "work(void*)" as work_spec with (pthread.starter_spec [tele] PreW PostW).
  cpp.spec "stopper(void*)" as stopper_spec with (pthread.starter_spec StopT PreS PostS).

  cpp.spec "test()" as test_spec with
    (\post{r}[Vint r] [| r = 0 \/ r = 1 |]).

  Lemma work_starter :
    work_spec |-- _global "work(void*)" |-> pthread.starter_specR [tele] PreW PostW.
  Proof. rewrite pthread.starter_specR.unlock. iIntros "H". iExact "H". Qed.
  Lemma stopper_starter :
    stopper_spec |-- _global "stopper(void*)" |-> pthread.starter_specR StopT PreS PostS.
  Proof. rewrite pthread.starter_specR.unlock. iIntros "H". iExact "H". Qed.

  Lemma work_ok : verify[join_other_thread_cpp.source] work_spec.
  Proof using MOD. verify_spec. go. Qed.

  (** S joins a thread it did not create. *)
  Lemma stopper_ok : verify[join_other_thread_cpp.source] stopper_spec.
  Proof using MOD.
    verify_spec. destruct arg as [γ [jtid [P []]]]; simpl. go.
    all: case_bool_decide; go.
  Qed.

  Lemma test_ok : verify[join_other_thread_cpp.source] test_spec.
  Proof using MOD.
    verify_spec.
    iDestruct select work_spec as "#Ws"; iDestruct (work_starter with "Ws") as "#?".
    iDestruct select stopper_spec as "#Ss"; iDestruct (stopper_starter with "Ss") as "#?".
    go.
    iExists _, PreW, PostW, taO; go.
    case_bool_decide; go; [| iPureIntro; lia].
    iExists _, PreS, PostS,
      (taS γt (taS tid (taS (count_addr |-> intR 1$m 1)%I taO)) : tele_arg StopT); go.
    (* S was created, or not and [test()] joins W itself. Each join may fail. *)
    all: case_bool_decide; go.
    all: case_bool_decide; go; iPureIntro; lia.
  Qed.

  (** The whole program, from the C++ library specs it uses. *)
  Theorem test_from_specs :
    denoteModule join_other_thread_cpp.source **
    pthread.create_spec ** pthread.join_spec ** abort_spec
    |-- test_spec.
  Proof using MOD.
    iIntros "(#M & #C & #J & #A)".
    iAssert work_spec as "#W". { iApply (work_ok with "M"). }
    iAssert stopper_spec as "#S". { iApply (stopper_ok with "M"); iFrame "#". }
    iApply (test_ok with "M"); iFrame "#".
  Qed.

End with_cpp.

