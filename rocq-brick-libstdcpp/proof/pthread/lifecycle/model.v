(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var.

Module lifecycle.

  (** A registry is the authority shared by the specifications for one process.
      A fresh registration starts a fresh generation of the installed thread ID.
      The Boolean key distinguishes the ID lease from the join right. *)
  Definition generation := iprop.gname.
  Definition registry := iprop.gname.
  Definition state := gmap (thread_idT * bool) generation.

  Inductive phase :=
  | IdentityOnly
  | Running
  | Complete (result : ptr)
  | Reaped (result : ptr).

  Class G (Σ : gFunctors) := {
    registry_G : ghost_mapG Σ (thread_idT * bool) generation;
    completion_G : ghost_varG Σ (thread_idT * phase);
  }.

  #[global] Existing Instances registry_G completion_G.

  Definition Σ : gFunctors :=
    #[ghost_mapΣ (thread_idT * bool) generation;
      ghost_varΣ (thread_idT * phase)].

  #[global] Instance subG_G Σ' : subG Σ Σ' -> G Σ'.
  Proof. solve_inG. Qed.

End lifecycle.
