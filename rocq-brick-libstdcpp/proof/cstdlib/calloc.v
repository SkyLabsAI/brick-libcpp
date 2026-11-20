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

(** * <<calloc>>

    Like <<malloc>>, but the block holds <<count * size>> zero bytes.
    <<calloc>> fails if <<count * size>> overflows <<size_t>>, so a
    successful call returns exactly that many bytes. The block may be given
    to <<free>> (its bytes become [blockR] by [array_sliceR_ucharR_blockR]). *)
Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ, !HasStdThreads Σ}.

  cpp.spec "calloc" as calloc_spec with
    (\arg{count} "__nmemb" (Vn count)
     \arg{size} "__size" (Vn size)
     \persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post{p e'}[Vptr p]
        errnoR th 1$m e' **
        if bool_decide (p = nullptr) then [| e' = ENOMEM |]
        else [| e' = e \/ e' <> 0 |] **
             [| valid<Tsize_t> (count * size)%N |] **
             p |-> (array_sliceR Tuchar 0 (count * size)%N
                      (fun b : Z => ucharR 1$m b)
                      (replicateZ (count * size)%N 0%Z) **
                    alignedR MALLOC_ALIGNMENT **
                    mallocatedR 1 (count * size))).
End with_cpp.
