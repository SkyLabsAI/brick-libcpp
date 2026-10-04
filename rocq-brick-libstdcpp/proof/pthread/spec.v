(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.

Require Export skylabs.bi.tls_modalities.

Require Import skylabs.auto.cpp.prelude.spec.

Module pthread_attr.
  Export pthread_attr.

  cpp.spec "pthread_attr_t::pthread_attr_t()"
    from source
    as ctor_spec
    with ( \this this
           \post this |-> pthread_attr.R 1$m None ).

  cpp.spec "pthread_attr_t::~pthread_attr_t()"
    from source
    as dtor_spec
    with ( \this this
           \pre{x} this |-> pthread_attr.R 1$m x
           \post emp ).

  cpp.spec "pthread_attr_init"
    as init_spec
    from source
    with (\arg{pattr} "attr" (Vptr pattr)
          \pre{attr}    pattr |-> pthread_attr.R 1$m attr
          \post[Vint 0] pattr |-> pthread_attr.R 1$m (Some pthread_attr.default)).

  cpp.spec "pthread_attr_destroy"
    as destroy_spec
    from source
    with (\arg{pattr} "attr" (Vptr pattr)
          \pre{attr}    pattr |-> pthread_attr.R 1$m attr
          \post[Vint 0] ∃ x, pattr |-> pthread_attr.R 1$m x).

End pthread_attr.

Module pthread.
  Export pthread.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Definition starter_kind : okind :=
      tFunction (cc:=CC_C) "void*" ["void*"%cpp_type].

  Definition starter_spec `{Σ : cpp_logic, σ : genv} `{!HasStdThreads Σ}
      (argT stateT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> ptr -> mpred)
      (Post_c : ptr -> argT -> stateT -> mpred) : WpSpec_cpp_val :=
    \arg{argp} "arg" (Vptr argp)
    \pre{arg} Pre argp arg
    \prepost{tid} current_thread tid
    \prepost{γ}   pthread.cancelation γ tid (Post_c argp arg)
    \post{retp}[Vptr retp] Post argp arg retp.

  mlock
  Definition starter_specR `{Σ : cpp_logic, σ : genv} `{!HasStdThreads Σ}
      (argT stateT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> ptr -> mpred)
      (Post_c : ptr -> argT -> stateT -> mpred) : Rep :=
    unmaterialized_specR starter_kind
      (starter_spec argT stateT Pre Post Post_c)  .

Section with_cpp.

  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ}.

  cpp.spec "pthread_create"
     as create_spec
     from source
     with ( \arg{idp}        "tid"   (Vptr idp)
            \pre{id0}         idp |-> oprimR "unsigned long" 1$m id0
            \arg{attrp}      "attr"  (Vptr attrp)
            \let attr := pthread_attr.default (* we limit ourselves to the standard flags for now *)
            \prepost{q_attr}  attrp |-> pthread_attr.R q_attr (Some attr)
            \arg{starterp}   "start" (Vptr starterp)
            \with argT stateT Pre Post Post_c
            \pre              starterp |-> starter_specR argT stateT Pre Post Post_c
            \arg{argp}       "arg"   (Vptr argp)
            \pre{arg : argT}  Pre argp arg
            \prepost{this_thread} current_thread this_thread
            \require WeaklyLocalWith procTI (Pre argp arg)
            \require forall retp, WeaklyLocalWith procTI (Post argp arg retp)
            \require ∀p.. s, WeaklyLocalWith procTI (Post_c argp arg s)
            \post{err}[Vint err]
               if bool_decide (err = 0) then
                 ∃ γt tid,
                   pthread.handle γt this_thread tid RunningOrCompleted
                       (Post argp arg) (bi_texist (Post_c argp arg)) ∗
                   idp |-> pthread.R 1$m tid
               else
                 Pre argp arg ∗
                 idp |-> oprimR "unsigned long" 1$m id0 ).

  cpp.spec "pthread_join"
     as join_spec
     from source
     with ( \arg{tid}      "tid"   (Vthread tid)
            \arg{retp}     "ret"   (Vptr retp)
            \pre{ret0}      retp |-> oprimR "void*" 1$m ret0
            \prepost{this_thread} current_thread this_thread
            \pre{γ s P Pc}  pthread.handle γ this_thread tid s P Pc
            \post[Vint 0] (* the precondition rules out the errors that [pthread_join] can report:
                              - deadlocks
                              - thread is not joinable (our specs don't allow us to create such threads yet)
                              - thread id does not designate an existing thread
                              - thread is being joined by other thread *)
               ∃ ret,
                 retp |-> ptrR<"void"> 1$m ret ∗
                 match s with
                 | RunningOrCompleted => P ret
                 | CanceledOrCompleted =>
                   ∃ pCANCELED,
                     canceled pCANCELED ∗
                     if bool_decide (ret = pCANCELED)
                       then Pc
                       else P ret
                 end ).

  cpp.spec "pthread_cancel"
     as cancel_spec
     from source
     with ( \arg{tid}     "tid"   (Vthread tid)
            \with spawner
            \pre{γ P Pc}  pthread.handle γ spawner tid RunningOrCompleted P Pc
            \post[Vint 0]
               pthread.handle γ spawner tid CanceledOrCompleted P Pc ).

  cpp.spec "pthread_testcancel"
     as testcancel_spec
     from source
     with ( \prepost{γ tid T Pc}  pthread.cancelation γ tid (T := T) Pc
            \prepost              current_thread tid
            \prepost{s}           Pc s
            \post emp ).

End with_cpp.
End pthread.
