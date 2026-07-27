(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.

Module optional_uint8_model.
  #[local] Open Scope Z_scope.

  (** An optional byte either contains no value or contains exactly one byte. *)
  Definition state : Type := option Z.

  Definition has_value (st : state) : bool :=
    match st with
    | None => false
    | Some _ => true
    end.

  
End optional_uint8_model.
