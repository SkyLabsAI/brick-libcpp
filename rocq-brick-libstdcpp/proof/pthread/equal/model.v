(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.pthread.lifecycle.spec.
Require Import skylabs.auto.cpp.prelude.pred.

Module pthread_equal_model.
  (** Linux x86-64 [int] is signed and 32 bits wide. POSIX leaves the
      particular nonzero result for equal, valid IDs unspecified. *)
  Definition result (a b : thread_idT) (ret : Z) : Prop :=
    (-2147483648 <= ret <= 2147483647)%Z /\
    (ret = 0%Z <-> a <> b).

  Lemma result_same tid ret : result tid tid ret -> ret <> 0%Z.
  Proof.
    intros [_ [different _]] zero.
    exact (different zero eq_refl).
  Qed.

  Lemma result_distinct a b ret :
    a <> b -> result a b ret -> ret = 0%Z.
  Proof.
    intros different [_ [_ zero]].
    exact (zero different).
  Qed.
End pthread_equal_model.
