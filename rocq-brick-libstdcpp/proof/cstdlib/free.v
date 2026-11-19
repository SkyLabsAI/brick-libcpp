(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.cstdlib.pred.
Require Import skylabs.brick.libstdcpp.cstdlib.inc_cstdlib_cpp.

#[local] Set Primitive Projections.

(** * <<free>>

    [p] must be NULL or the start of a live block from <<malloc>>, given
    back whole together with its [mallocatedR] token. <<free(NULL)>> does
    nothing. <<free>> does not touch [errno]. Bytes written by the program
    can be given back with [array_sliceR_ucharR_blockR]. *)
Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  cpp.spec "free" as free_spec with
    (\arg{p} "__ptr" (Vptr p)
     \pre if bool_decide (p = nullptr) then emp
          else ∃ sz, p |-> (mallocatedR 1 sz ** blockR sz 1$m)
     \post emp).
End with_cpp.
