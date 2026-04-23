(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.cstring.model.

#[local] Set Primitive Projections.

#[local] Open Scope Z_scope.

(** [object_bytesR byte_ty q bytes] is an abstract counted byte view of an
    object range. The payload is the unsigned-byte values observed by the
    memory functions; [byte_ty] records the one-byte pointer-stepping type used
    for returned interior pointers. *)
Axiom object_bytesR : forall `{Σ : cpp_logic} {σ : genv},
  type -> cQp.t -> list Z -> Rep.

Axiom object_bytesR_cfrac : forall `{Σ : cpp_logic} {σ : genv} byte_ty bytes,
  CFractional (fun q => object_bytesR byte_ty q bytes).
#[global] Existing Instance object_bytesR_cfrac.

#[global] Instance object_bytesR_as_cfrac `{Σ : cpp_logic, σ : genv}
    byte_ty q bytes :
  AsCFractional (object_bytesR byte_ty q bytes)
    (fun q => object_bytesR byte_ty q bytes) q.
Proof. solve_as_cfrac. Qed.

(** [object_bytes_anyR byte_ty n] owns a writable [n]-byte destination range
    whose previous byte values are irrelevant. *)
Axiom object_bytes_anyR : forall `{Σ : cpp_logic} {σ : genv},
  type -> Z -> Rep.

Axiom object_bytesR_to_arrayLR : forall `{Σ : cpp_logic} {σ : genv}
    (p : ptr) ty q hi bytes,
  lengthZ bytes = hi ->
  p |-> object_bytesR ty q bytes ⊢
  p |-> arrayLR ty 0 hi (fun b : Z => ucharR q b) bytes.

Axiom object_bytesR_of_arrayLR : forall `{Σ : cpp_logic} {σ : genv}
    (p : ptr) ty q hi bytes,
  lengthZ bytes = hi ->
  p |-> arrayLR ty 0 hi (fun b : Z => ucharR q b) bytes ⊢
  p |-> object_bytesR ty q bytes.

Axiom object_bytes_anyR_of_anyR_array : forall `{Σ : cpp_logic} {σ : genv}
    (p : ptr) ty n,
  p |-> anyR (Tarray ty n) 1$m ⊢
  p |-> object_bytes_anyR ty (Z.of_N n).
