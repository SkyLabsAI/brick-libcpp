(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.cerrno.pred.
Require Export skylabs.brick.libstdcpp.cstdlib.pred.
Require Import skylabs.brick.libstdcpp.cstdlib.inc_cstdlib_cpp.

#[local] Set Primitive Projections.

(** * <<malloc>>

    A successful call returns fresh storage of [sz] bytes, aligned to
    [MALLOC_ALIGNMENT], together with the allocator's meta-data
    [mallocatedR 1 sz]. Distinct live blocks are disjoint because their
    ownership is separate.

    A size of 0 is allowed: the result is either NULL or a unique pointer
    to an empty block.

    On failure the result is NULL and [errno] is <<ENOMEM>>. On success,
    C11 7.5p3 allows [errno] to be set to any nonzero value, so callers only
    learn that it is unchanged or nonzero. *)
Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ, !HasStdThreads Σ}.

  cpp.spec "malloc" as malloc_spec with
    (\arg{sz} "__size" (Vn sz)
     \persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post{p e'}[Vptr p]
        errnoR th 1$m e' **
        if bool_decide (p = nullptr) then [| e' = ENOMEM |]
        else [| e' = e \/ e' <> 0 |] **
             p |-> (blockR sz 1$m **
                    alignedR MALLOC_ALIGNMENT **
                    mallocatedR 1 sz)).
End with_cpp.
