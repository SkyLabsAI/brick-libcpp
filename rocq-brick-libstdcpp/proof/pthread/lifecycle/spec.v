(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.lifecycle.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.iris.extra.proofmode.proofmode.

(** Shared vocabulary for the downstream callable contracts. Import the installed
    pthread specifications separately for the legacy creator/NULL protocol. *)
Module lifecycle_join.
  Definition slot_arg (slot : option ptr) : ptr :=
    match slot with
    | None => nullptr
    | Some p => p
    end.

  Section result_slot.
    Context `{Σ : cpp_logic, σ : genv}.

    (** A writable [void **] points to full owned storage for a [void *].
        [old = None] admits allocated uninitialized storage. *)
    Definition slot_before (slot : option ptr) (old : option val) : mpred :=
      match slot with
      | None => emp
      | Some p => ⌜p <> nullptr⌝ ∗ p |-> oprimR "void*" 1$m old
      end%I.

    Definition slot_after (slot : option ptr) (result : ptr) : mpred :=
      match slot with
      | None => emp
      | Some p => ⌜p <> nullptr⌝ ∗ p |-> oprimR "void*" 1$m (Some (Vptr result))
      end%I.

    Lemma discard_before old : slot_before None old ⊣⊢ emp.
    Proof. reflexivity. Qed.

    Lemma discard_after result : slot_after None result ⊣⊢ emp.
    Proof. reflexivity. Qed.

    Lemma writable_before p old :
      slot_before (Some p) old ⊣⊢ ⌜p <> nullptr⌝ ∗ p |-> oprimR "void*" 1$m old.
    Proof. reflexivity. Qed.

    Lemma writable_after p result :
      slot_after (Some p) result ⊢ p |-> oprimR "void*" 1$m (Some (Vptr result)).
    Proof. rewrite /slot_after. iIntros "[_ H]". iExact "H". Qed.
  End result_slot.
End lifecycle_join.
