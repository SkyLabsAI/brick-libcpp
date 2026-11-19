(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.lifecycle.model.
From iris.base_logic.lib Require Export ghost_var.
From stdpp Require Import namespaces.
Require Import skylabs.iris.extra.proofmode.proofmode.

Module pthread_create.
  (** Process setup selects the registry. All external contracts for the
      process share that name through the ambient context. *)
  Class ProcessRegistry := {
    registry_name : lifecycle.registry;
  }.

  Definition registry_namespace : namespace := nroot .@ "pthread-registry".
  Definition completion_namespace : namespace := nroot .@ "pthread-completion".
End pthread_create.
