(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.optional.spec.

(**
   Automation for clients of [std::optional<unsigned char>].

   The representation predicate [optional_uint8.R] is sealed, so the byte
   cell that an engaged optional owns is not visible to the automation at a
   call site.  Every client that reads through <<operator*>> therefore needs
   the same resource step.  The hints below supply it once for the whole
   package instead of leaving each client proof to restate it.
 *)

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (**
     An engaged optional owns the byte cell located at the very address its
     dereference hands back.  This exchange lets a read through an engaged
     optional discharge automatically, instead of requiring the
     representation to be unsealed by hand at every call site.
   *)
  #[program] Definition optional_uint8_R_engaged_byte_C
      (o p : ptr) (q : cQp.t) (b : Z) :=
    \cancelx
    \consuming o |-> optional_uint8.R q (Some b) (Some p)
    \proving p |-> ucharR q b
    \end.
  Next Obligation.
    intros.
    rewrite optional_uint8.R.unlock.
    rewrite _at_sep _at_pureR.
    go.
  Qed.
End with_cpp.

(**
   Two observations of the same optional agree on the contained byte, which
   lets repeated reads share a single value.
 *)
#[export] Instance optional_uint8_R_read_learn `{Σ : cpp_logic, σ : genv} :
  AtLearnEq3 optional_uint8.R := ltac:(solve_learnable).

#[export] Hint Resolve optional_uint8_R_engaged_byte_C : br_hints.
#[export] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.
