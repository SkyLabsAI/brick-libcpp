(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.join.pred.
Require skylabs.brick.libstdcpp.pthread.inc_hpp.
Require Import skylabs.auto.cpp.prelude.spec.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.pthread.inc_hpp.source.

Module pthread_join.
  Export pthread_join.
  Section external.
    Context `{Σ : cpp_logic, σ : genv}.
    Context `{!HasStdThreads Σ, !lifecycle.G _Σ, !pthread_create.ProcessRegistry}.
    Context `{!ProcessWaitDiscipline}.

    (** Partial correctness for a distinct, sole joiner of an unreaped,
        registered joinable target in the same process. The supplied wait
        bound excludes a path from target to joiner, so adding the proposed
        join edge cannot close a cycle. A non-NULL result pointer requires
        a writable slot. The coordinated lifecycle protocol requires
        recollecting every ID-lease fraction before retiring the generation:
        reaping cannot invalidate a framed borrower fraction. POSIX can
        permit an otherwise valid join even when the model has borrowers.

        Process setup supplies the same sealed registry synchronization used
        by pthread_create. At the external join boundary, claim_completion
        can be attempted while the target is still running; a pending claim
        returns the completion right. A ready claim and reap_completed
        recover the normal callback result and its associated resources.
        The caller needs no prior observation of termination.

        Synchronization transfers the independent join right between peers
        using the process-local laws for the resource. This contract does
        not cover competing joins, invalid/detached targets, self or cyclic
        waits, cancellation, non-normal worker exit, or error-code diagnostics.
        It does not assert progress, fairness, or bounded waiting. *)
    #[local] cpp.spec "pthread_join"
      from source
      as join_spec
      with ( \arg{tid : thread_idT} "__th" (Vthread tid)
             \arg{slot : option ptr} "__thread_return"
               (Vptr (lifecycle_join.slot_arg slot))
             \prepost{joiner : thread_idT} current_thread joiner
             \require (joiner <> tid)
             \require (~ may_wait_path tid joiner)
             \prepost pthread_create.registry_sync pthread_create.registry_name
             \pre{g : lifecycle.generation}
               lifecycle.id_valid pthread_create.registry_name 1 tid g
             \pre{Post : ptr -> mpred}
               pthread_create.completion_right pthread_create.registry_name tid g Post
             \pre{old : option val} lifecycle_join.slot_before slot old
             \post{result : ptr}[Vint 0]
               lifecycle.joined tid g result ∗ Post result ∗
                 lifecycle_join.slot_after slot result ).
  End external.
End pthread_join.
