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

(** The alignment of every block returned by <<malloc>>: C11 7.22.3p1
    requires it to suit any type with a fundamental alignment, i.e.
    <<alignof(max_align_t)>>.

    glibc-specific (x86-64): this is <<MALLOC_ALIGNMENT>>, 16. We state it as a
    constant because <<max_align_t>> contains a <<long double>>, whose alignment
    the C++ semantics does not compute. *)
Definition MALLOC_ALIGNMENT : N := 16.

(** The value <<malloc>> stores in [errno] when it fails (POSIX).
    Linux/glibc-specific: <<ENOMEM>> is 12. *)
Definition ENOMEM : Z := 12.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (** The allocation meta-data of a block returned by <<malloc>>, **owned by
      the allocator**: [mallocatedR q sz] at the returned pointer records that
      the block holds [sz] bytes.

      In a normal implementation, this is a few bytes before the returned
      pointer that store, e.g., the size of the allocation.

      Owning [mallocatedR 1 sz] is the right to give the block back to the
      allocator exactly once. It is distinct from the token of
      <<operator new>> ([allocatedR] in [new.pred]), so memory from <<malloc>>
      cannot be passed to <<operator delete>>. *)
  Parameter mallocatedR : forall {σ : genv}, Qp -> N -> Rep.
  #[only(fractional,asfractional,fracvalid,timeless)] derive mallocatedR.
  #[global] Instance: Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) mallocatedR).
  Proof. solve_learnable. Qed.
End with_cpp.
