(*
 * Copyright (c) 2025-2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.elpi.derive.bi.

#[local] Set Primitive Projections.

(** <cstdlib> does not introduce any types. This file holds the resources
    of the C allocation functions. *)

(** The alignment of every block returned by <<malloc>> and <<calloc>>:
    C11 7.22.3p1 requires it to suit any type with a fundamental alignment,
    i.e. <<alignof(max_align_t)>>.

    glibc-specific (x86-64): this is <<MALLOC_ALIGNMENT>>, 16. We state it as a
    constant because <<max_align_t>> contains a <<long double>>, whose alignment
    the C++ semantics does not compute. *)
Definition MALLOC_ALIGNMENT : N := 16.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (** The allocation meta-data of a block returned by <<malloc>> or
      <<calloc>>, **owned by the allocator**: [mallocatedR q sz] at the returned pointer records that
      the block holds [sz] bytes.

      In a normal implementation, this is a few bytes before the returned
      pointer that store, e.g., the size of the allocation.

      Owning [mallocatedR 1 sz] is the right to pass the pointer to <<free>>
      exactly once. It is distinct from the token of
      <<operator new>> ([allocatedR] in [new.pred]), so memory from <<malloc>>
      cannot be passed to <<operator delete>> and vice versa. *)
  Parameter mallocatedR : forall {σ : genv}, Qp -> N -> Rep.
  #[only(fractional,asfractional,fracvalid,timeless)] derive mallocatedR.
  #[global] Instance: Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) mallocatedR).
  Proof. solve_learnable. Qed.
End with_cpp.

(** Initialized bytes can be given back as raw storage, e.g. to <<free>>
    bytes written by the program. *)
#[export] Hint Resolve array_sliceR_ucharR_blockR_C : br_hints.
