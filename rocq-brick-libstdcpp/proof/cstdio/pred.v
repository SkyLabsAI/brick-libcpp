(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.iostream.pred.

#[local] Set Primitive Projections.

(** * <cstdio> output streams

    A C stream ([FILE]) that is open for writing is described like an
    [<ostream>]: by an [Ostream], the handler that receives each byte
    written to it (see [iostream/README.md]). *)
Module cfile.
  Parameter gname : Set.

  (** [R OS γ q] at a [FILE] object: an open stream whose output goes to
      [OS]. It is distinct from [ostream.R], so a [FILE] cannot be used as a
      C++ stream or vice versa. *)
  Parameter R : forall `{Σ : cpp_logic} {σ : genv}, Ostream -> gname -> cQp.t -> Rep.
  #[only(cfracsplittable)] derive R.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    #[global] Instance: Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.
  End with_cpp.
End cfile.
