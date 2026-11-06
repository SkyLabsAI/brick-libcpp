(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.cerrno.pred.
Require Import skylabs.brick.libstdcpp.cerrno.inc_cerrno_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ, !HasStdThreads Σ}.

  (** glibc-specific: [errno] is [( *__errno_location ())]. The result depends
      only on the calling thread, which justifies glibc's
      [__attribute__((const))]. *)
  cpp.spec "__errno_location" with
    (\persist{th} current_thread th
     (* The cell is a live [int] for the whole lifetime of [th]. *)
     \post[Vptr (errno_loc th)] errno_loc th |-> type_ptrR "int").
End with_cpp.

(** Library functions documented to set [errno] take [errnoR th 1 e] and
    return it updated; C11 7.5p3 lets any function set [errno] nonzero unless
    its description says otherwise, so specs that do not mention [errno]
    assume (glibc-specific, trusted) that it is left alone. *)
