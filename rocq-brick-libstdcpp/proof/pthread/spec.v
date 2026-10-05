(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.

Require Export skylabs.bi.tls_modalities.

Require Import skylabs.auto.cpp.prelude.spec.

Module pthread.
  Export pthread.
  Import auto.telescopes auto.telescopes.TeleNotations.

  (** [pthread] specs

      This module specifies thread creation and joining. Unsupported are the following features of
      pthread:
      - detaching threads;
      - canceling threads;
      - joining a thread by threads other than their creator.

      This prevents possible deadlocks when joining threads or race conditions when two threads both
      try to cancel the same thread.
   *)

  Definition starter_kind : okind :=
      tFunction (cc:=CC_C) "void*" ["void*"%cpp_type].

  Definition starter_spec `{Σ : cpp_logic, σ : genv} `{!HasStdThreads Σ}
      (argT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> thread_idT -> mpred) : WpSpec_cpp_val :=
    \arg{argp} "arg" (Vptr argp)
    \prepost{tid} current_thread tid
    \pre{arg} Pre argp arg
    \post[Vptr nullptr] Post argp arg tid.

  mlock
  Definition starter_specR `{Σ : cpp_logic, σ : genv} `{!HasStdThreads Σ}
      (argT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> thread_idT -> mpred) : Rep :=
    unmaterialized_specR starter_kind
      (starter_spec argT Pre Post)  .

Section with_cpp.

  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ}.

  cpp.spec "pthread_t::pthread_t()"
    from source
    as ctor_spec
    with ( \this this
           \post ∃ tid, this |-> pthread.R 1$m tid ).

  cpp.spec "pthread_t::~pthread_t()"
    from source
    as dtor_spec
    inline.

  cpp.spec "pthread_create"
     as create_spec
     from source
     with ( \arg{idp}        "tid"   (Vptr idp)
            \pre{id0}         idp |-> oprimR "unsigned long" 1$m id0
            \arg             "attr"  (Vptr nullptr)
            \arg{starterp}   "start" (Vptr starterp)
            \with argT Pre Post
            \pre              starterp |-> starter_specR argT Pre Post
            \arg{argp}       "arg"   (Vptr argp)
            \pre{arg : argT}  Pre argp arg
            \with this_thread
            \prepost          current_thread this_thread
            \require WeaklyLocalWith procTI (Pre argp arg)
            \require forall tid, WeaklyLocalWith procTI (Post argp arg tid)
            \post{err}[Vint err]
               if bool_decide (err = 0) then
                 ∃ γt tid,
                   pthread.handle γt this_thread tid (Post argp arg tid) ∗
                   idp |-> pthread.R 1$m tid
               else
                 Pre argp arg ∗
                 idp |-> oprimR "unsigned long" 1$m id0 ).

  cpp.spec "pthread_join"
     as join_spec
     from source
     with ( \arg{tid}      "tid"   (Vthread tid)
            \arg           "ret"   (Vptr nullptr)
            \prepost{this_thread} current_thread this_thread
            \pre{γ P}      pthread.handle γ this_thread tid P
            \post[Vint 0] (* the precondition rules out the errors that [pthread_join] can report:
                              - deadlocks
                              - thread is not joinable (our specs don't allow us to create such threads yet)
                              - thread id does not designate an existing thread
                              - thread is being joined by other thread *)
                 P ).

End with_cpp.
End pthread.
