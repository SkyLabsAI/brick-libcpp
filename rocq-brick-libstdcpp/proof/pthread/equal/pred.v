(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.equal.model.
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.iris.extra.proofmode.proofmode.

Module pthread_equal_pred.
  Section operands.
    Context `{Σ : cpp_logic, !lifecycle.G _Σ}.

    (** Exactly one lease suffices for two copies of one modeled ID. Distinct
        IDs have independent leases in the designated process registry.
        Fractions are returned unchanged by the comparison. *)
    Local Definition operands_def (r : lifecycle.registry) (a b : thread_idT)
        (qa qb : Qp) (ga gb : lifecycle.generation) : mpred :=
      if decide (a = b)
      then lifecycle.id_valid r qa a ga
      else lifecycle.id_valid r qa a ga ** lifecycle.id_valid r qb b gb.

    Local Definition operands_sealed : seal (@operands_def).
    Proof. by eexists. Qed.

    Definition operands := operands_sealed.(unseal).
    Local Definition operands_unseal : operands = @operands_def :=
      operands_sealed.(seal_eq).

    Lemma operands_same r tid qa qb ga gb :
      operands r tid tid qa qb ga gb -|- lifecycle.id_valid r qa tid ga.
    Proof.
      rw operands_unseal /operands_def decide_True //.
    Qed.

    Lemma operands_distinct r a b qa qb ga gb :
      a <> b ->
      operands r a b qa qb ga gb -|-
        lifecycle.id_valid r qa a ga ** lifecycle.id_valid r qb b gb.
    Proof.
      intros different.
      rw operands_unseal /operands_def decide_False //.
    Qed.
  End operands.

  #[global] Hint Opaque operands : sl_opacity.
End pthread_equal_pred.
