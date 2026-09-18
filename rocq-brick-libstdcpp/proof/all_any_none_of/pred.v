(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.all_any_none_of.model.

NES.Begin all_any_none_of.

(* [state k] describes the predicate's separate resources after [k] calls. *)
#[global] Abbreviation predicate_spec xs test I :=
  ((fun (values : list Z) (accepts : Z -> option bool) (state : Z -> mpred) =>
    unmaterialized_fspec (tFunction Tbool [Tuchar])
      (\with (k : Z)
       \arg{x} "b" (Vint x)
       \require (0 <= k)%Z
       \require (k < lengthZ values)%Z
       \require x ∈ values
       \pre state k
       \post{r : bool}[Vbool r] state (k + 1)%Z **
         match accepts x with Some b => [| r = b |] | None => emp end))
    xs test I) (only parsing).

NES.End all_any_none_of.
